use crate::utils::poly::*;
use halo2_common::arithmetic::lagrange_interpolate;
use halo2_common::halo2curves::group::Group;
use halo2_liam_eagen_msm::regular_functions_utils::Grumpkin;
use halo2_liam_eagen_msm::regular_functions_utils::*;
use halo2_proofs::arithmetic::*;
use halo2_proofs::halo2curves::ff::PrimeField;
use halo2_proofs::halo2curves::CurveExt;
use rand::rngs::ThreadRng;
use std::marker::PhantomData;
use std::vec;

#[derive(Clone)]
// function field element represented by a(x)-yb(x), how about Lagrange?
pub struct FunctionField<F: PrimeField, C: CurveExt<Base = F>> {
    pub a: Poly<F>,
    pub b: Poly<F>,
    _marker: PhantomData<C>,
}

#[allow(dead_code)]
impl<F: PrimeField, C: CurveExt<Base = F>> FunctionField<F, C> {
    pub fn identity() -> Self {
        Self {
            a: Poly::<F>::one(),
            b: Poly::<F>::zero(),
            _marker: PhantomData,
        }
    }

    // line represented by y=\lambda x + \mu
    pub fn line(lambda: F, mu: F) -> Self {
        let a = Poly {
            coeff: vec![mu, lambda],
        };
        let b = Poly::constant(F::ONE);
        Self {
            a,
            b,
            _marker: PhantomData,
        }
    }

    // output (lambda, mu) such that y=\lambda x + \mu is the tangent line at the point
    pub fn tangent_line(pt: C) -> (F, F) {
        let (x, y) = to_xy(pt);
        let lambda = ((x + x + x) * x + C::a()) * (y + y).invert().unwrap();
        // this fails if y(P) = 0
        let mu = y - lambda * x;
        (lambda, mu)
    }

    // output (lambda, mu) such that y=\lambda x + \mu is the secant line at two points
    pub fn secant_line(pt1: C, pt2: C) -> Option<(F, F)> {
        let (x0, y0) = to_xy(pt1);
        let (x1, y1) = to_xy(pt2);
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
    pub fn another_zero_of_line(lambda: F, mu: F, pt1: C, pt2: C) -> C {
        let x1 = to_x(pt1);
        let x2 = to_x(pt2);
        let x3 = lambda.square() - x1 - x2;
        let y3 = lambda * x3 + mu;
        C::new_jacobian(x3, y3, C::Base::ONE).unwrap()
    }

    pub fn evaluate(&self, point: C) -> F {
        let (x, y) = to_xy(point);
        self.a.evaluate(x) - y * self.b.evaluate(x)
    }

    pub fn is_zero_at(&self, point: C) -> bool {
        self.evaluate(point) == F::ZERO
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
            std::cmp::max(a, b)
        }
    }

    pub fn deg_display(&self) -> (usize, usize, usize) {
        (self.a.deg(), self.b.deg(), self.deg())
    }

    pub fn mul_with_line(&self, lambda: F, mu: F) -> Self {
        let line = Poly::from_vec(vec![mu, lambda]);
        Self {
            a: &self.a * &line + &self.b * Poly::from_vec(vec![C::b(), C::a()]) + &self.b.shift(3),
            b: &self.b * line + &self.a,
            _marker: PhantomData,
        }
    }

    pub fn mul_with_vertical_line(&self, x: F) -> Self {
        Self {
            a: self.a.mul_with_linear(-x),
            b: self.b.mul_with_linear(-x),
            _marker: PhantomData,
        }
    }
    pub fn divide_by_vertical_line(&self, x: F) -> Self {
        Self {
            a: self.a.div_by_linear(-x),
            b: self.b.div_by_linear(-x),
            _marker: PhantomData,
        }
    }

    // given "distinct" points, output interpolation using Half-GCD.
    // todo: make it into general version.
    pub fn interpolate_mumford_distinct(points: &[C]) -> Self {
        let (u, v) = Self::mumford_repn_distinct(points);
        let (_, (c, b)) = Poly::half_gcd(&u, &v);
        let mut a = u * c + v * &b;
        a.clear();

        let out = Self {
            a,
            b,
            _marker: PhantomData,
        };

        assert_eq!(out.deg(), points.len(), "points are not distinct");
        out
    }

    // given semi-reduced "distinct" points, find mumford representation.
    fn mumford_repn_distinct(points: &[C]) -> (Poly<F>, Poly<F>) {
        let (px, py): (Vec<F>, Vec<F>) = points.iter().map(|&p| to_xy(p)).unzip();

        let v = lagrange_interpolate(&px, &py);

        let u = px.iter().fold(Poly::one(), |acc, &next| {
            acc * Poly::from_vec(vec![-next, F::ONE])
        });

        (u, Poly::from_vec(v))
    }

    // given points with one repetition on the last point, output interpolation using Half-GCD.
    pub fn interpolate_mumford(_points: &[C], _repeat: usize) -> Self {
        todo!()
    }
    // given points with one repetition on the last point, find mumford representation.
    fn mumford_repn(_points: &[C]) -> (Poly<F>, Poly<F>) {
        todo!()
    }

    // todo: parallelize
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
                    f = f.mul_with_vertical_line(to_x(pt1));
                }
            }
            while to_divide.len() >= 2 {
                let pt1 = to_divide.pop().unwrap();
                let pt2 = to_divide.pop().unwrap();

                if let Some((lambda, mu)) = Self::secant_line(-pt1, -pt2) {
                    f = f.mul_with_line(lambda, mu);
                    to_divide.push(Self::another_zero_of_line(lambda, mu, pt1, pt2));
                    f = f.divide_by_vertical_line(to_x(pt1));
                    f = f.divide_by_vertical_line(to_x(pt2));
                } else {
                    // pt1 = -pt2
                    f = f.divide_by_vertical_line(to_x(pt1));
                }
            }
        }
        assert_eq!(points.len(), f.deg());

        f
    }

    #[cfg(test)]
    // only for test. this clones derivates for each time.
    pub fn evaluate_derivative(&self, point: C) -> F {
        let (x, y) = to_xy(point);

        let a_prime = self.a.derivative().evaluate(x);
        let b_prime = self.b.derivative().evaluate(x);

        let tmp = ((x + x + x) * x + C::a()) * (y + y).invert().unwrap();

        a_prime - tmp * self.b.evaluate(x) - y * b_prime
    }

    #[cfg(test)]
    pub fn check_interpolate(&self, points: &[C]) {
        assert_eq!(self.deg(), points.len());
        for pt in points.iter() {
            assert!(self.is_zero_at(*pt));
        }
    }

    // todo: scalar should be in Fr
    // second output: the inner product
    pub fn ecip_interpolate(scalars: &[isize], points: &[C]) -> (Vec<FunctionField<F, C>>, C) {
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
                            q[j] += points[i];
                            to_interpolate[j].push(-points[i]);
                        }
                        1 => {
                            q[j] -= points[i];
                            to_interpolate[j].push(points[i]);
                        }
                        _ => {}
                    }
                }
            }
        }

        for j in (0..l - 1).rev() {
            q[j] = -(q[j + 1] + q[j + 1] + q[j + 1]) + q[j];
        }

        let mut divisor_witness: Vec<FunctionField<F, C>> = vec![];

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

fn to_xy<C: CurveExt>(pt: C) -> (C::Base, C::Base) {
    let coord = pt.jacobian_coordinates();
    let z_inv = coord.2.invert().unwrap();
    (coord.0 * z_inv, coord.1 * z_inv)
}

fn to_x<C: CurveExt>(pt: C) -> C::Base {
    let coord = pt.jacobian_coordinates();
    coord.0 * coord.2.invert().unwrap()
}

impl<C: CurveExt> FunctionField<C::Base, C>
where
    C::Base: FftPrecomp,
{
    pub fn interpolate_lev(points: &[C]) -> Self {
        // todo: remove to_vec
        let f = compute_divisor_witness(points.to_vec());
        Self {
            a: Poly::from_vec(f.a.poly),
            b: -Poly::from_vec(f.b.poly),
            _marker: PhantomData,
        }
    }

    pub fn ecip_interpolate_lev(
        scalars: &[isize],
        points: &[C],
    ) -> (Vec<FunctionField<C::Base, C>>, C) {
        let n = points.len();
        assert_eq!(n, scalars.len());

        let mut exponent: Vec<Vec<isize>> = vec![];
        for scalar in scalars.iter() {
            exponent.push(minus_three_adic(*scalar));
        }

        let l = exponent
            .iter()
            .map(|a| a.len())
            .max_by(|x, y| x.cmp(y))
            .unwrap();
        let mut q: Vec<C> = vec![C::identity(); l];
        let mut to_interpolate: Vec<Vec<C>> = vec![vec![]; l];
        for j in 0..l {
            for i in 0..n {
                if let Some(exp) = exponent[i].get(j) {
                    match exp {
                        -1 => {
                            q[j] += points[i];
                            to_interpolate[j].push(-points[i]);
                        }
                        1 => {
                            q[j] -= points[i];
                            to_interpolate[j].push(points[i]);
                        }
                        _ => {}
                    }
                }
            }
        }

        for j in (0..l - 1).rev() {
            q[j] = -(q[j + 1] + q[j + 1] + q[j + 1]) + q[j];
        }

        let mut divisor_witness: Vec<FunctionField<C::Base, C>> = vec![];

        for j in 0..l - 1 {
            to_interpolate[j].push(q[j]);
            to_interpolate[j].push(q[j + 1]);
            to_interpolate[j].push(q[j + 1]);
            to_interpolate[j].push(q[j + 1]);
            let f = Self::interpolate_lev(&to_interpolate[j]);
            divisor_witness.push(f);
        }

        to_interpolate[l - 1].push(q[l - 1]);
        divisor_witness.push(Self::interpolate_lev(&to_interpolate[l - 1]));

        (divisor_witness, -q[0])
    }
}

// for test, random points P_i such that \sum P_i = O
pub fn random_points_sum_zero(rng: &mut ThreadRng, n: usize) -> Vec<Grumpkin> {
    let mut points = random_points(rng, n - 1);
    let sum = points
        .iter()
        .skip(1)
        .fold(points[0], |acc, next| (acc + next));
    points.push(-sum);

    points
}

// for test, random points P_i
pub fn random_points(rng: &mut ThreadRng, n: usize) -> Vec<Grumpkin> {
    let mut points: Vec<Grumpkin> = vec![];
    for _ in 0..n {
        points.push(Grumpkin::random(rng.clone()));
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

pub fn curve_scalar_mul<C: CurveExt>(scalar: isize, point: C) -> C {
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
            point += point;
        } else {
            out += point;
            scalar /= 2;
            point = point + point;
        }
    }
    out
}

pub fn curve_inner_product<C: CurveExt>(scalars: &[isize], points: &[C]) -> C {
    assert_eq!(scalars.len(), points.len());
    scalars
        .iter()
        .zip(points.iter())
        .fold(C::identity(), |acc, next| {
            acc + curve_scalar_mul(*next.0, *next.1)
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

pub fn into_field<F: PrimeField>(a: isize) -> F {
    if a < 0 {
        -F::from_u128(-a as u128)
    } else {
        F::from_u128(a as u128)
    }
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
            "{} points mumford interpolate in {}ms",
            n,
            cur_time.elapsed().unwrap().as_millis()
        );
        f.check_interpolate(&points);
    }

    #[test]
    fn test_interpolate_incremental() {
        // generate P_i such that \sum P_i = O.
        let rng = &mut thread_rng();
        let n = 3000;
        let points = random_points_sum_zero(rng, n);

        // interpolate P_i
        let cur_time = SystemTime::now();
        let f = FunctionField::interpolate_incremental(&points);
        println!(
            "{} points incremental interpolate in {}ms",
            n,
            cur_time.elapsed().unwrap().as_millis()
        );
        f.check_interpolate(&points);
    }

    #[test]
    fn test_interpolate_lev() {
        // generate P_i such that \sum P_i = O.
        let rng = &mut thread_rng();
        let n = 10000;
        let points = random_points_sum_zero(rng, n);

        // interpolate P_i
        let cur_time = SystemTime::now();
        let f = FunctionField::interpolate_lev(&points);
        println!(
            "{} points incremental interpolate in {}ms",
            n,
            cur_time.elapsed().unwrap().as_millis()
        );
        f.check_interpolate(&points);
    }

    // todo: check which is faster, for desirable n
    #[test]
    fn compare_interpolate() {
        // generate P_i such that \sum P_i = O.
        let rng = &mut thread_rng();
        let n = 5000;
        let points = random_points_sum_zero(rng, n);

        // interpolate P_i with mumford reprensentation
        let cur_time = SystemTime::now();
        let f = FunctionField::interpolate_mumford_distinct(&points);
        println!(
            "{} points mumford interpolate in {}ms",
            n,
            cur_time.elapsed().unwrap().as_millis()
        );
        for i in 0..points.len() {
            assert!(f.is_zero_at(points[i]));
        }

        // interpolate P_i with incremental method
        let cur_time = SystemTime::now();
        let f = FunctionField::interpolate_incremental(&points);
        println!(
            "{} points incremental interpolate in {}ms",
            n,
            cur_time.elapsed().unwrap().as_millis()
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
            .fold(points[0], |acc, next| (acc + next));
        points.push(-sum);
        assert_eq!(points.len(), n);

        let cur_time = SystemTime::now();
        let f = FunctionField::interpolate_incremental(&points);
        println!(
            "interpolate in {}ms",
            cur_time.elapsed().unwrap().as_millis()
        );
        f.check_interpolate(&points);
    }
}
