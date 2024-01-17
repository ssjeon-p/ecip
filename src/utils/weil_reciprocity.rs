use crate::utils::function_field::*;
use halo2_proofs::{arithmetic::Field, halo2curves::CurveAffine};

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
        let (x1, y1) = Self::to_xy(pts.0);
        let (x2, y2) = Self::to_xy(pts.1);
        assert_ne!(x1, x2);

        let (lambda, mu) = FunctionField::secant_line(pts.0, pts.1).unwrap();
        let pt3 = FunctionField::another_zero_of_line(lambda, mu, pts.0, pts.1);
        let (x3, y3) = Self::to_xy(pt3);

        let d1 = ((x1 + x1 + x1) * x1 + C::a()) * (y1 + y1).invert().unwrap();
        let d2 = ((x2 + x2 + x2) * x2 + C::a()) * (y2 + y2).invert().unwrap();
        let d3 = ((x3 + x3 + x3) * x3 + C::a()) * (y3 + y3).invert().unwrap();

        Self {
            mu,
            lambda,
            points: [pts.0, pts.1, pt3],
            dx_dy: [d1, d2, d3],
        }
    }

    pub fn from_higher(pt: C) -> Self {
        let (lambda, mu) = FunctionField::tangent_line(pt);
        let pt3 = FunctionField::another_zero_of_line(lambda, mu, pt, pt);
        let (x3, y3) = Self::to_xy(pt3);

        let d3 = ((x3 + x3 + x3) * x3 + C::a()) * (y3 + y3).invert().unwrap();

        Self {
            mu,
            lambda,
            points: [pt, pt, pt3],
            dx_dy: [lambda, lambda, d3],
        }
    }

    // evaluate dx/dz at point
    pub fn dx_dz_simple(pt: C, lambda: C::Base) -> C::Base {
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

pub fn trace_simple<C: CurveAffine>(point: C, clg: &MSMChallenge<C>) -> C::Base {
    let pt = point.coordinates().unwrap();
    (clg.mu + clg.lambda * *pt.x() - *pt.y()).invert().unwrap()
}

pub fn trace_higher<C: CurveAffine>(point: C, clg: &MSMChallenge<C>) -> C::Base {
    let pt = point.coordinates().unwrap();
    let x0 = *clg.points[0].coordinates().unwrap().x();
    (x0 - *pt.x()) * (clg.mu + clg.lambda * *pt.x() - *pt.y()).invert().unwrap()
}

#[cfg(test)]
mod test {
    use super::*;
    use halo2_proofs::halo2curves::secp256k1::{Fp, Secp256k1Affine};
    use rand::thread_rng;

    #[test]
    fn test_simple_challenge() {
        // divisor witness
        let n = 200;
        let rng = &mut thread_rng();
        let points = random_points_sum_zero(rng, n);
        let f = FunctionField::interpolate_incremental(&points);

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

        let lhs = field_inner_product(&dx_dz, &d_prime_d);
        let rhs = points.iter().fold(Fp::ZERO, |acc, &next| {
            acc + trace_simple::<Secp256k1Affine>(next, &clg)
        });

        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_higher_challenge() {
        // divisor witness
        let n = 200;
        let rng = &mut thread_rng();
        let points = random_points_sum_zero(rng, n);
        let f = FunctionField::interpolate_mumford_distinct(&points);

        // random challenge
        let rng = &mut thread_rng();
        let pt = Secp256k1Affine::random(rng);
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

    #[test]
    fn test_ecip_simple() {
        let n = 200;
        let rng = &mut thread_rng();
        let points = random_points(rng, n);

        let mut scalars = vec![];
        for _ in 0..n {
            scalars.push(rand::random::<isize>() % -10000);
        }

        let pt1 = Secp256k1Affine::random(rng.clone());
        let pt2 = Secp256k1Affine::random(rng.clone());
        let clg = MSMChallenge::from_simple((pt1, pt2));

        let mut lhs = Fp::ZERO;
        let mut digit = Fp::ONE;
        let (divisor_witness, prod) = FunctionField::ecip_interpolate(&scalars, &points);
        assert_eq!(prod, curve_inner_product(&scalars, &points));

        let dx_dz: Vec<Fp> = clg
            .points
            .into_iter()
            .map(|pt| MSMChallenge::dx_dz_simple(pt, clg.lambda))
            .collect();

        for f in divisor_witness.iter() {
            let d_prime_d: Vec<Fp> = clg
                .points
                .into_iter()
                .map(|pt| f.evaluate_derivative(pt) * f.evaluate(pt).invert().unwrap())
                .collect();
            lhs += digit * field_inner_product(&dx_dz, &d_prime_d);
            digit = -digit - digit - digit;
        }

        let mut trace = trace_simple(-prod, &clg);
        for i in 0..n {
            let (a, b) = split_num(scalars[i]);
            trace += field_scalar_mul(a, trace_simple(points[i], &clg));
            trace += field_scalar_mul(b, trace_simple(-points[i], &clg));
        }
        assert_eq!(lhs, trace);
    }

    #[test]
    fn test_ecip_higher() {
        let n = 200;
        let rng = &mut thread_rng();
        let points = random_points(rng, n);

        let mut scalars = vec![];
        for _ in 0..n {
            scalars.push(rand::random::<isize>() % -10000);
        }

        let pt = Secp256k1Affine::random(rng.clone());
        let clg = MSMChallenge::from_higher(pt);
        let c2 = clg.higher_c2();
        let c2_lam = c2 + clg.lambda + clg.lambda;

        // equation (3) in (https://eprint.iacr.org/2022/596)
        let mut lhs = Fp::ZERO;
        let mut digit = Fp::ONE;
        let (divisor_witness, prod) = FunctionField::ecip_interpolate(&scalars, &points);
        assert_eq!(prod, curve_inner_product(&scalars, &points));
        for f in divisor_witness.iter() {
            let d_prime_d_0 =
                f.evaluate_derivative(clg.points[0]) * f.evaluate(clg.points[0]).invert().unwrap();
            let d_prime_d_2 =
                f.evaluate_derivative(clg.points[2]) * f.evaluate(clg.points[2]).invert().unwrap();
            lhs += digit * (c2 * d_prime_d_2 - c2_lam * d_prime_d_0);
            digit = -digit - digit - digit;
        }

        let mut trace = trace_higher(-prod, &clg);
        for i in 0..n {
            let (a, b) = split_num(scalars[i]);
            trace += field_scalar_mul(a, trace_higher(points[i], &clg));
            trace += field_scalar_mul(b, trace_higher(-points[i], &clg));
        }

        assert_eq!(lhs, trace);
    }
}
