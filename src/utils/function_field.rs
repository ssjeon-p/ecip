use crate::utils::poly::*;
use halo2_proofs::arithmetic::*;
use halo2_proofs::halo2curves::group::Curve;
use halo2_proofs::halo2curves::secp256k1::Secp256k1Affine;
use rand::rngs::ThreadRng;
use std::cmp::max;
use std::vec;

#[derive(Clone)]
// function field element represented by a(x)-yb(x), how about Lagrange?
pub struct FunctionField<C: CurveAffine> {
    pub a: Poly<C::Base>,
    pub b: Poly<C::Base>,
}

#[allow(dead_code)]
impl<C: CurveAffine> FunctionField<C> {
    pub fn identity() -> Self {
        Self {
            a: Poly::<C::Base>::one(),
            b: Poly::<C::Base>::zero(),
        }
    }

    // line represented by y=\lambda x + \mu
    pub fn line(lambda: C::Base, mu: C::Base) -> Self {
        let a = Poly { coeff: vec![mu, lambda] };
        let b = Poly::constant(C::Base::ONE);
        Self { a, b }
    }

    fn to_xy(pt: C) -> (C::Base, C::Base) {
        let coord = pt.coordinates().unwrap();
        (*coord.x(), *coord.y())
    }

    // output (lambda, mu) such that y=\lambda x + \mu is the tangent line at the point
    pub fn tangent_line(pt: C) -> (C::Base, C::Base) {
        let (x, y) = Self::to_xy(pt);
        let lambda = ((x + x + x) * x + C::a()) * (y + y).invert().unwrap();
        // this fails if y(P) = 0
        let mu = y - lambda * x;
        (lambda, mu)
    }

    // output (lambda, mu) such that y=\lambda x + \mu is the secant line at two points
    pub fn secant_line(pt1: C, pt2: C) -> Option<(C::Base, C::Base)> {
        let (x0, y0) = Self::to_xy(pt1);
        let (x1, y1) = Self::to_xy(pt2);
        if x0 == x1 {
            if y0 == y1 {
                Some(Self::tangent_line(pt1))
            } else {
                None
            }
        } else {
            let lambda = (y0 - y1) * (x0 - x1).invert().unwrap();
            let mu = y0 - lambda * x0;
            Some((lambda, mu))
        }
    }

    // this actually ouputs -(pt1+pt2). but efficient with knowledge of lambda and mu
    pub fn another_zero_of_line(lambda: C::Base, mu: C::Base, pt1: C, pt2: C) -> C {
        let x1 = *pt1.coordinates().unwrap().x();
        let x2 = *pt2.coordinates().unwrap().x();
        let x3 = lambda.square() - x1 - x2;
        let y3 = lambda * x3 + mu;
        CurveAffine::from_xy(x3, y3).unwrap()
    }

    pub fn evaluate(&self, point: C) -> C::Base {
        let coord = point.coordinates().unwrap();
        let x = *coord.x();
        let y = *coord.y();

        self.a.evaluate(x) - y * self.b.evaluate(x)
    }

    pub fn is_zero_at(&self, point: C) -> bool {
        self.evaluate(point) == C::Base::ZERO
    }

    // degree of function field (equal to the degree of O, point at infinity)
    pub fn deg(&self) -> usize {
        let a = 2 * self.a.deg();
        let b = 2 * self.b.deg() + 3;
        if self.a.is_zero() {
            b
        } else if self.b.is_zero() {
            a
        } else {
            max(a, b)
        }
    }

    fn deg_display(&self) -> (usize, usize, usize) {
        (self.a.deg(), self.b.deg(), self.deg())
    }

    // multiply with a line y=\lambda x + \mu
    // todo: maybe this can be optimized, remove mul with one
    pub fn mul_with_line(&self, lambda: C::Base, mu: C::Base) -> Self {
        let line = Poly::from_vec(vec![mu, lambda]);
        let defining_curve = Poly::from_vec(vec![C::b(), C::a(), C::Base::ZERO, C::Base::ONE]);
        Self {
            a: &self.a * &line + &self.b * defining_curve,
            b: &self.b * line + &self.a,
        }
    }

    // todo: maybe this can be optimized, remove mul with one
    pub fn mul_with_vertical_line(&self, x: C::Base) -> Self {
        let line = Poly::vertical_line(x);
        Self {
            a: &self.a * &line,
            b: &self.b * line,
        }
    }

    // todo: maybe this can be optimized, remove divide with one
    pub fn divide_by_vertical_line(&self, x: C::Base) -> Self {
        let line = Poly::vertical_line(x);
        Self {
            a: Poly::euclidean(&self.a, &line).0,
            b: Poly::euclidean(&self.b, &line).0,
        }
    }

    // given "distinct" points, output interpolation using Half-GCD.
    // todo: make it into general version.
    pub fn interpolate_mumford_distinct(points: &[C]) -> Self {
        let (u, v) = Self::mumford_repn_distinct(points);
        let (_, (c, mut b)) = Poly::half_gcd(&u, &v);
        let mut a = u * c + v * &b;
        a.clear();

        // this is for circuit. to make a.len == b.len. todo: remove this
        b.coeff
            .extend_from_slice(&[C::Base::ZERO, C::Base::ZERO, C::Base::ZERO]);
        let out = Self { a, b };

        assert_eq!(out.deg(), points.len(), "points are not distinct");
        out
    }

    // given semi-reduced "distinct" points, find mumford representation.
    fn mumford_repn_distinct(points: &[C]) -> (Poly<C::Base>, Poly<C::Base>) {
        let (px, py): (Vec<C::Base>, Vec<C::Base>) = points
            .iter()
            .map(|&p| {
                let coord = p.coordinates().unwrap();
                (*coord.x(), *coord.y())
            })
            .unzip();

        let v = lagrange_interpolate(&px, &py);

        let u = px.iter().fold(Poly::one(), |acc, &next| {
            acc * Poly::from_vec(vec![-next, C::Base::ONE])
        });

        (u, Poly::from_vec(v))
    }

    // given points with one repetition on the last point, output interpolation using Half-GCD.
    pub fn interpolate_mumford(_points: &[C], _repeat: usize) -> Self {
        todo!()
    }
    // given points with one repetition on the last point, find mumford representation.
    fn mumford_repn(_points: &[C]) -> (Poly<C::Base>, Poly<C::Base>) {
        todo!()
    }

    // given points, find interpolation using incremental method.
    pub fn interpolate_incremental(points: &[C]) -> Self {
        let mut to_interpolate = points.to_vec();
        let mut to_divide: Vec<C> = vec![];
        let mut f = Self::identity();

        while to_interpolate.len() >= 2 {
            while to_interpolate.len() >= 2 {
                let pt1 = to_interpolate.pop().unwrap();
                let pt2 = to_interpolate.pop().unwrap();
                if let Some((lambda, mu)) = Self::secant_line(pt1, pt2) {
                    f = f.mul_with_line(lambda, mu);
                    to_divide.push(Self::another_zero_of_line(lambda, mu, pt1, pt2));
                } else {
                    // pt1 = -pt2
                    f = f.mul_with_vertical_line(*pt1.coordinates().unwrap().x());
                }
            }
            while to_divide.len() >= 2 {
                let pt1 = to_divide.pop().unwrap();
                let pt2 = to_divide.pop().unwrap();

                if let Some((lambda, mu)) = Self::secant_line(-pt1, -pt2) {
                    f = f.mul_with_line(lambda, mu);
                    to_divide.push(Self::another_zero_of_line(lambda, mu, pt1, pt2));
                    f = f.divide_by_vertical_line(*pt1.coordinates().unwrap().x());
                    f = f.divide_by_vertical_line(*pt2.coordinates().unwrap().x());
                } else {
                    // pt1 = -pt2
                    f = f.divide_by_vertical_line(*pt1.coordinates().unwrap().x());
                }
            }
        }
        assert_eq!(points.len(), f.deg());

        f
    }

    // only for test. this clones derivates for each time.
    pub fn evaluate_derivative(&self, point: C) -> C::Base {
        let coord = point.coordinates().unwrap();
        let (x, y) = (*coord.x(), *coord.y());

        let a_prime = self.a.derivative().evaluate(x);
        let b_prime = self.b.derivative().evaluate(x);

        let tmp = ((x + x + x) * x + C::a()) * (y + y).invert().unwrap();

        a_prime - tmp * self.b.evaluate(x) - y * b_prime
    }

    // for test
    fn check_interpolate(&self, points: &[C]) {
        assert_eq!(self.deg(), points.len());
        for pt in points.iter() {
            assert!(self.is_zero_at(*pt));
        }
    }

    // second output: the inner product
    pub fn ecip_interpolate(scalars: &[isize], points: &[C]) -> (Vec<FunctionField<C>>, C) {
        let n = points.len();
        assert_eq!(n, scalars.len());

        let mut exponent: Vec<Vec<isize>> = vec![];
        for scalar in scalars.iter() {
            exponent.push(minus_three_adic(*scalar));
        }

        let l = exponent.iter().map(|a| a.len()).max().unwrap();
        let mut q: Vec<C> = vec![C::identity(); l];
        let mut to_interpolate: Vec<Vec<C>> = vec![vec![]; l];
        for j in 0..l {
            for i in 0..n {
                if let Some(exp) = exponent[i].get(j) {
                    match exp {
                        -1 => {
                            q[j] = (q[j] + points[i]).into();
                            to_interpolate[j].push(-points[i]);
                        }
                        1 => {
                            q[j] = (q[j] - points[i]).into();
                            to_interpolate[j].push(points[i]);
                        }
                        _ => {}
                    }
                }
            }
        }

        for j in (0..l - 1).rev() {
            q[j] = (-(q[j + 1] + q[j + 1] + q[j + 1]) + q[j]).into();
        }

        let mut divisor_witness: Vec<FunctionField<C>> = vec![];

        for j in 0..l - 1 {
            to_interpolate[j].push(q[j]);
            to_interpolate[j].push(q[j + 1]);
            to_interpolate[j].push(q[j + 1]);
            to_interpolate[j].push(q[j + 1]);
            let f = Self::interpolate_incremental(&to_interpolate[j]);
            divisor_witness.push(f);
        }

        to_interpolate[l - 1].push(q[l - 1]);
        divisor_witness.push(Self::interpolate_incremental(&to_interpolate[l - 1]));

        (divisor_witness, -q[0])
    }
}

// for test, random points P_i such that \sum P_i = O
pub fn random_points_sum_zero(rng: &mut ThreadRng, n: usize) -> Vec<Secp256k1Affine> {
    let mut points = random_points(rng, n - 1);
    let sum = points
        .iter()
        .skip(1)
        .fold(points[0], |acc, next| (acc + next).to_affine());
    points.push(-sum);

    points
}

// for test, random points P_i
pub fn random_points(rng: &mut ThreadRng, n: usize) -> Vec<Secp256k1Affine> {
    let mut points: Vec<Secp256k1Affine> = vec![];
    for _ in 0..n {
        points.push(Secp256k1Affine::random(rng.clone()));
    }
    points
}

pub fn field_inner_product<F: Field>(a: &[F], b: &[F]) -> F {
    assert_eq!(a.len(), b.len());
    a.iter()
        .zip(b.iter())
        .fold(F::ZERO, |acc, next| acc + *next.0 * *next.1)
}

pub fn field_scalar_mul<F: Field>(scalar: isize, point: F) -> F {
    let mut scalar = scalar;
    let mut point = point;
    let mut out = F::ZERO;

    if scalar < 0 {
        scalar = -scalar;
        point = -point;
    }

    while scalar != 0 {
        if scalar % 2 == 0 {
            scalar /= 2;
            point = point + point;
        } else {
            out += point;
            scalar /= 2;
            point = point + point;
        }
    }
    out
}

pub fn curve_scalar_mul<C: CurveAffine>(scalar: isize, point: C) -> C {
    let mut scalar = scalar;
    let mut point = point;
    let mut out = C::identity();

    if scalar < 0 {
        scalar = -scalar;
        point = -point;
    }

    while scalar != 0 {
        if scalar % 2 == 0 {
            scalar /= 2;
            point = (point + point).into();
        } else {
            out = (out + point).into();
            scalar /= 2;
            point = (point + point).into();
        }
    }
    out
}

pub fn curve_inner_product<C: CurveAffine>(scalars: &[isize], points: &[C]) -> C {
    assert_eq!(scalars.len(), points.len());
    scalars
        .iter()
        .zip(points.iter())
        .fold(C::identity(), |acc, next| {
            (acc + curve_scalar_mul(*next.0, *next.1)).into()
        })
}

// Given integer, output (v_j) such that num = \sum_{j=0} v_j (-3)^j
pub fn minus_three_adic(num: isize) -> Vec<isize> {
    let mut out: Vec<isize> = vec![];
    let mut num = num;

    while num != 0 {
        let rem;
        (num, rem) = div_mod(num);
        out.push(rem);
    }
    out
}

// Given integer, output (a, b) such that num = a - b, and each -3-adic digit of a,b are zero or one.
pub fn split_num(num: isize) -> (isize, isize) {
    let exponent = minus_three_adic(num);
    let mut digit = 1;
    let (mut a, mut b) = (0, 0);
    for exp in exponent.iter() {
        match exp {
            -1 => {
                b += digit;
            }
            1 => {
                a += digit;
            }
            _ => {}
        }
        digit *= -3;
    }
    (a, b)
}

pub fn div_mod(num: isize) -> (isize, isize) {
    let (quot, rem) = (num / -3, num % -3);
    match rem {
        -2 => (quot + 1, 1),
        2 => (quot - 1, -1),
        _ => (quot, rem),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use rand::thread_rng;
    use std::time::SystemTime;

    #[test]
    fn test_interpolate_mumford_distinct() {
        // generate P_i such that \sum P_i = O.
        let rng = &mut thread_rng();
        let n = 200;
        let points = random_points_sum_zero(rng, n);

        // interpolate P_i
        let cur_time = SystemTime::now();
        let f = FunctionField::interpolate_mumford_distinct(&points);
        println!(
            "{} points mumford interpolate in {}s",
            n,
            cur_time.elapsed().unwrap().as_secs()
        );
        f.check_interpolate(&points);
    }

    #[test]
    fn test_interpolate_incremental() {
        // generate P_i such that \sum P_i = O.
        let rng = &mut thread_rng();
        let n = 200;
        let points = random_points_sum_zero(rng, n);

        // interpolate P_i
        let cur_time = SystemTime::now();
        let f = FunctionField::interpolate_incremental(&points);
        println!(
            "{} points incremental interpolate in {}s",
            n,
            cur_time.elapsed().unwrap().as_secs()
        );
        f.check_interpolate(&points);
    }

    // todo: check which is faster, for desirable n
    #[test]
    fn compare_interpolate() {
        // generate P_i such that \sum P_i = O.
        let rng = &mut thread_rng();
        let n = 200;
        let points = random_points_sum_zero(rng, n);

        // interpolate P_i with mumford reprensentation
        let cur_time = SystemTime::now();
        let f = FunctionField::interpolate_mumford_distinct(&points);
        println!(
            "{} points mumford interpolate in {}s",
            n,
            cur_time.elapsed().unwrap().as_secs()
        );
        for i in 0..points.len() {
            assert!(f.is_zero_at(points[i]));
        }

        // interpolate P_i with incremental method
        let cur_time = SystemTime::now();
        let f = FunctionField::interpolate_incremental(&points);
        println!(
            "{} points incremental interpolate in {}s",
            n,
            cur_time.elapsed().unwrap().as_secs()
        );
        f.check_interpolate(&points);
    }

    #[test]
    fn test_interpolate_repeated_points() {
        let n = 200;
        let rng = &mut thread_rng();
        let mut points = random_points(rng, n - 3);
        points.push(points[n - 4]);
        points.push(points[n - 4]);
        let sum = points
            .iter()
            .skip(1)
            .fold(points[0], |acc, next| (acc + next).to_affine());
        points.push(-sum);
        assert_eq!(points.len(), n);

        let cur_time = SystemTime::now();
        let f = FunctionField::interpolate_incremental(&points);
        println!("interpolate in {}s", cur_time.elapsed().unwrap().as_secs());
        f.check_interpolate(&points);
    }
}
