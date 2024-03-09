use crate::utils::function_field::*;
use halo2_proofs::arithmetic::Field;
use halo2curves::CurveExt;
use num::integer::Roots;

#[derive(Debug, Default, Clone)]
pub struct MSMChallenge<C: CurveExt> {
    pub mu: C::Base,
    pub lambda: C::Base,
    pub points: [C; 3],
    pub dx_dy: [C::Base; 3],
}

#[allow(dead_code)]
impl<C: CurveExt> MSMChallenge<C> {
    pub fn from_simple(pts: (C, C)) -> Self {
        let (x1, y1) = to_xy(pts.0);
        let (x2, y2) = to_xy(pts.1);
        assert_ne!(x1, x2);

        let (lambda, mu) = FunctionField::secant_line(pts.0, pts.1).unwrap();
        let pt3 = FunctionField::another_zero_of_line(lambda, mu, pts.0, pts.1);
        let (x3, y3) = to_xy(pt3);

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
        let (x3, y3) = to_xy(pt3);

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
        let (x, y) = to_xy(pt);
        (((x + x + x) * x + C::a()) * (y + y).invert().unwrap() - lambda)
            .invert()
            .unwrap()
    }

    pub fn higher_c2(&self) -> C::Base {
        let x0 = to_xy(self.points[0]).0;
        let (x2, y2) = to_xy(self.points[2]);
        ((y2 + y2) * (x0 - x2))
            * ((x2 + x2 + x2) * x2 + C::a() - (y2 + y2) * self.lambda)
                .invert()
                .unwrap()
    }
}

fn to_xy<C: CurveExt>(pt: C) -> (C::Base, C::Base) {
    let (x, y, z) = pt.jacobian_coordinates();
    let z_inv = z.invert().unwrap();
    let z_inv_sq = z_inv * z_inv;
    (x * z_inv_sq, y * z_inv_sq * z_inv)
}

pub fn trace_simple<C: CurveExt>(point: C, clg: &MSMChallenge<C>) -> C::Base {
    let (x, y) = to_xy(point);
    (clg.mu + clg.lambda * x - y).invert().unwrap()
}

pub fn trace_higher<C: CurveExt>(point: C, clg: &MSMChallenge<C>) -> C::Base {
    let (x, y) = to_xy(point);
    let x0 = to_xy(clg.points[0]).0;
    (x0 - x) * (clg.mu + clg.lambda * x - y).invert().unwrap()
}

// given third root of unity w \in Fr, split scalar = a + w b into short a,b
// lattice reduction method in https://link.springer.com/chapter/10.1007/3-540-44647-8_11
pub fn split_cm(scalar: Vec<isize>, l: isize, n: isize) -> Vec<(isize, isize)> {
    // euclidean algorithm
    let mut s = vec![1, 0];
    let mut t = vec![0, 1];
    let mut r = vec![n, l];
    let mut v2 = (0, 0);
    let mut v1 = (0, 0);

    let sqrt_n = n.sqrt();

    for i in 1.. {
        let quot = r[i - 1] / r[i];
        r.push(r[i - 1] - quot * r[i]);
        s.push(s[i - 1] - quot * s[i]);
        t.push(t[i - 1] - quot * t[i]);
        if r[i] < sqrt_n {
            v1 = (r[i], -t[i]);
            v2 = (r[i - 1], -t[i - 1]);
            let v3 = (r[i + 1], -t[i + 1]);
            if norm_sq(v3) < norm_sq(v2) {
                v2 = v3;
            }
            break;
        }
    }
    assert_eq!((v1.0 + l * v1.1) % n, 0);
    assert_eq!((v2.0 + l * v2.1) % n, 0);

    let det = v1.0 * v2.1 - v1.1 * v2.0;

    let mut out = vec![];
    for k in scalar.iter() {
        let b1 = nearest_int(v2.1 * k, det);
        let b2 = nearest_int(-v1.1 * k, det);
        out.push((k - b1 * v1.0 - b2 * v2.0, -b1 * v1.1 - b2 * v2.1));
    }

    out
}

fn norm_sq(a: (isize, isize)) -> isize {
    a.0 * a.0 + a.1 * a.1
}

// nearest interger of a/b
fn nearest_int(a: isize, b: isize) -> isize {
    if a % b < b / 2 {
        a / b
    } else {
        a / b + 1
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use halo2_liam_eagen_msm::regular_functions_utils::Grumpkin;
    use halo2curves::{group::Group, grumpkin::Fq};

    use rand::thread_rng;

    #[test]
    fn test_simple_challenge() {
        // divisor witness
        let n = 5000;
        let rng = &mut thread_rng();
        let points = random_points_sum_zero(rng, n);
        let f = FunctionField::interpolate_lev(&points);

        // random challenge
        let rng = &mut thread_rng();
        let pt0 = Grumpkin::random(rng.clone());
        let pt1 = Grumpkin::random(rng.clone());
        let clg = MSMChallenge::from_simple((pt0, pt1));

        // equation (1) in (https://eprint.iacr.org/2022/596)
        let dx_dz: [Fq; 3] = [
            MSMChallenge::dx_dz_simple(clg.points[0], clg.lambda),
            MSMChallenge::dx_dz_simple(clg.points[1], clg.lambda),
            MSMChallenge::dx_dz_simple(clg.points[2], clg.lambda),
        ];

        // todo: this compute f, f' 3 times
        let d_prime_d: [Fq; 3] = [
            f.evaluate_derivative(clg.points[0]) * f.evaluate(clg.points[0]).invert().unwrap(),
            f.evaluate_derivative(clg.points[1]) * f.evaluate(clg.points[1]).invert().unwrap(),
            f.evaluate_derivative(clg.points[2]) * f.evaluate(clg.points[2]).invert().unwrap(),
        ];

        let lhs = field_inner_product(&dx_dz, &d_prime_d);
        let rhs = points.iter().fold(Fq::ZERO, |acc, &next| {
            acc + trace_simple::<Grumpkin>(next, &clg)
        });

        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_higher_challenge() {
        // divisor witness
        let n = 5000;
        let rng = &mut thread_rng();
        let points = random_points_sum_zero(rng, n);
        let f = FunctionField::interpolate_lev(&points);

        // random challenge
        let rng = &mut thread_rng();
        let pt = Grumpkin::random(rng);
        let clg = MSMChallenge::from_higher(pt);

        // equation (2) in (https://eprint.iacr.org/2022/596)
        let c2 = clg.higher_c2();
        let d_prime_d_0 =
            f.evaluate_derivative(clg.points[0]) * f.evaluate(clg.points[0]).invert().unwrap();
        let d_prime_d_2 =
            f.evaluate_derivative(clg.points[2]) * f.evaluate(clg.points[2]).invert().unwrap();
        let rhs = c2 * d_prime_d_2 - (c2 + clg.lambda + clg.lambda) * d_prime_d_0;
        let lhs = points.iter().fold(Fq::ZERO, |acc, &next| {
            acc + trace_higher::<Grumpkin>(next, &clg)
        });

        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_ecip_simple() {
        let n = 5000;
        let rng = &mut thread_rng();
        let points = random_points(rng, n);

        let mut scalars = vec![];
        for _ in 0..n {
            scalars.push(rand::random::<isize>() % -10000);
        }

        let pt1 = Grumpkin::random(rng.clone());
        let pt2 = Grumpkin::random(rng.clone());
        let clg = MSMChallenge::from_simple((pt1, pt2));

        let mut lhs = Fq::ZERO;
        let mut digit = Fq::ONE;
        let (divisor_witness, prod) = FunctionField::ecip_interpolate_lev(&scalars, &points);
        assert_eq!(prod, curve_inner_product(&scalars, &points));

        let dx_dz: Vec<Fq> = clg
            .points
            .into_iter()
            .map(|pt| MSMChallenge::dx_dz_simple(pt, clg.lambda))
            .collect();

        for f in divisor_witness.iter() {
            let d_prime_d: Vec<Fq> = clg
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
        let n = 5000;
        let rng = &mut thread_rng();
        let points = random_points_sum_zero(rng, n);

        let mut scalars = vec![];
        for _ in 0..n {
            scalars.push(rand::random::<isize>() % -10000);
        }

        let pt = Grumpkin::random(rng.clone());
        let clg = MSMChallenge::from_higher(pt);
        let c2 = clg.higher_c2();
        let c2_lam = c2 + clg.lambda + clg.lambda;

        // equation (3) in (https://eprint.iacr.org/2022/596)
        let mut lhs = Fq::ZERO;
        let mut digit = Fq::ONE;
        let (divisor_witness, prod) = FunctionField::ecip_interpolate_lev(&scalars, &points);
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
            trace += into_field::<Fq>(a) * trace_higher(points[i], &clg);
            trace += into_field::<Fq>(b) * trace_higher(-points[i], &clg);
        }

        assert_eq!(lhs, trace);
    }
}
