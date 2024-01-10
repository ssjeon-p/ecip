use crate::utils::function_field::Poly;
use halo2_proofs::{arithmetic::Field, halo2curves::CurveAffine};

#[allow(dead_code)]
#[derive(Debug, Default, Clone)]
pub struct MSMChallenge<C: CurveAffine> {
    pub mu: C::Base,
    pub lambda: C::Base,
    pub points: [C; 3],
    pub dx_dy: [C::Base; 3],
}

#[allow(dead_code)]
impl<C: CurveAffine> MSMChallenge<C> {
    pub fn from_simple(pts: (C, C)) -> Self {
        let (x0, y0) = Self::to_xy(pts.0);
        let (x1, y1) = Self::to_xy(pts.1);
        assert_ne!(x0, x1);

        let lambda = (y0 - y1) * (x0 - x1).invert().unwrap();
        let mu = y0 - lambda * x0;

        let poly = Poly::from_vec(vec![
            C::b() - mu.square(),
            C::a() - lambda * (mu + mu),
            -lambda.square(),
            C::Base::ONE,
        ]);

        let x3 = poly.another_zero(&[x0, x1]);
        let y3 = lambda * x3 + mu;
        let pt3 = CurveAffine::from_xy(x3, y3).unwrap();

        let d0 = ((x0 + x0 + x0) * x0 + C::a()) * (y0 + y0).invert().unwrap();
        let d1 = ((x1 + x1 + x1) * x1 + C::a()) * (y1 + y1).invert().unwrap();
        let d2 = ((x3 + x3 + x3) * x3 + C::a()) * (y3 + y3).invert().unwrap();

        Self {
            mu,
            lambda,
            points: [pts.0, pts.1, pt3],
            dx_dy: [d0, d1, d2],
        }
    }

    pub fn from_higher(pt: C) -> Self {
        let (x, y) = Self::to_xy(pt);
        let lambda = ((x + x + x) * x + C::a()) * (y + y).invert().unwrap();
        let mu = y - lambda * x;

        let poly = Poly::from_vec(vec![
            C::b() - mu.square(),
            C::a() - lambda * (mu + mu),
            -lambda.square(),
            C::Base::ONE,
        ]);

        let x3 = poly.another_zero(&[x, x]);
        let y3 = lambda * x3 + mu;
        let pt3 = CurveAffine::from_xy(x3, y3).unwrap();

        let d2 = ((x3 + x3 + x3) * x3 + C::a()) * (y3 + y3).invert().unwrap();

        Self {
            mu,
            lambda,
            points: [pt, pt, pt3],
            dx_dy: [lambda, lambda, d2],
        }
    }

    // evaluate dx/dz at point
    fn dx_dz_simple(pt: C, lambda: C::Base) -> C::Base {
        let (x, y) = Self::to_xy(pt);
        (((x + x + x) * x + C::a()) * (y + y).invert().unwrap() - lambda)
            .invert()
            .unwrap()
    }

    fn to_xy(pt: C) -> (C::Base, C::Base) {
        let coord = pt.coordinates().unwrap();
        (*coord.x(), *coord.y())
    }

    pub fn higher_c2(&self) -> C::Base {
        let x0 = *self.points[0].coordinates().unwrap().x();
        let (x2, y2) = Self::to_xy(self.points[2]);
        ((y2 + y2) * (x0 - x2))
            * ((x2 + x2 + x2) * x2 + C::a() - (y2 + y2) * self.lambda)
                .invert()
                .unwrap()
    }
}

#[allow(dead_code)]
pub fn trace_simple<C: CurveAffine>(point: C, clg: &MSMChallenge<C>) -> C::Base {
    let pt = point.coordinates().unwrap();
    (clg.mu + clg.lambda * *pt.x() - *pt.y()).invert().unwrap()
}

#[allow(dead_code)]
pub fn trace_higher<C: CurveAffine>(point: C, clg: &MSMChallenge<C>) -> C::Base {
    let pt = point.coordinates().unwrap();
    let x0 = *clg.points[0].coordinates().unwrap().x();
    (x0 - *pt.x()) * (clg.mu + clg.lambda * *pt.x() - *pt.y()).invert().unwrap()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::utils::function_field::*;
    use halo2_proofs::halo2curves::secp256k1::{Fp, Secp256k1Affine};
    use rand::thread_rng;

    #[test]
    fn test_simple_challenge() {
        // divisor witness
        let rng = &mut thread_rng();
        let points = random_points(rng, 45);
        let f = FunctionField::interpolate_mumford(&points);

        // random challenge
        let rng = &mut thread_rng();
        let pt0 = Secp256k1Affine::random(rng.clone());
        let pt1 = Secp256k1Affine::random(rng.clone());
        let clg = MSMChallenge::from_simple((pt0, pt1));

        // equation (1) in (https://eprint.iacr.org/2022/596)
        let dx_dz: Vec<Fp> = clg
            .points
            .into_iter()
            .map(|pt| MSMChallenge::dx_dz_simple(pt, clg.lambda))
            .collect();

        let d_prime_d: Vec<Fp> = clg
            .points
            .into_iter()
            .map(|pt| f.evaluate_derivative(pt) * f.evaluate(pt).invert().unwrap())
            .collect();

        let lhs = dx_dz
            .iter()
            .zip(d_prime_d.iter())
            .fold(Fp::ZERO, |acc, next| acc + *next.0 * *next.1);
        let rhs = points.iter().fold(Fp::ZERO, |acc, &next| {
            acc + trace_simple::<Secp256k1Affine>(next, &clg)
        });

        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_higher_challenge() {
        // divisor witness
        let rng = &mut thread_rng();
        let points = random_points(rng, 45);
        let f = FunctionField::interpolate_mumford(&points);

        // random challenge
        let rng = &mut thread_rng();
        let pt = Secp256k1Affine::random(rng.clone());
        let clg = MSMChallenge::from_higher(pt);

        // equation (2) in (https://eprint.iacr.org/2022/596)
        let c2 = clg.higher_c2();
        let d_prime_d_0 =
            f.evaluate_derivative(clg.points[0]) * f.evaluate(clg.points[0]).invert().unwrap();
        let d_prime_d_2 =
            f.evaluate_derivative(clg.points[2]) * f.evaluate(clg.points[2]).invert().unwrap();
        let rhs = c2 * d_prime_d_2 - (c2 + clg.lambda + clg.lambda) * d_prime_d_0;
        let lhs = points.iter().fold(Fp::ZERO, |acc, &next| {
            acc + trace_higher::<Secp256k1Affine>(next, &clg)
        });

        assert_eq!(lhs, rhs);
    }
}
