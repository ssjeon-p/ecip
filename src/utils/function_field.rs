use halo2_proofs::arithmetic::*;
use halo2_proofs::halo2curves::ff::PrimeField;
use halo2_proofs::halo2curves::group::Curve;
use halo2_proofs::halo2curves::secp256k1::Secp256k1Affine;
use rand::rngs::ThreadRng;
use std::ops::{Add, Mul, Neg};
use std::vec;

#[derive(Clone, Debug, PartialEq)]
pub struct Poly<F: PrimeField> {
    pub coeff: Vec<F>,
}

type PolyVec<F> = (Poly<F>, Poly<F>);
type PolyMat<F> = ((Poly<F>, Poly<F>), (Poly<F>, Poly<F>));

#[allow(dead_code)]
impl<F: PrimeField> Poly<F> {
    pub fn new() -> Self {
        Self { coeff: vec![] }
    }

    pub fn one() -> Self {
        Self {
            coeff: vec![F::ONE],
        }
    }

    pub fn zero() -> Self {
        Self {
            coeff: vec![F::ZERO],
        }
    }

    pub fn deg(&self) -> usize {
        if let Some(deg) = self.coeff.iter().rev().position(|&a| a != F::ZERO) {
            self.coeff.len() - deg - 1
        } else {
            0
        }
    }

    pub fn from_vec(coeff: Vec<F>) -> Self {
        Self { coeff }
    }

    pub fn constant(value: F) -> Self {
        Self::from_vec(vec![value])
    }

    // output coeff * x^deg
    pub fn monomial(deg: usize, coeff: F) -> Self {
        let mut out = vec![F::ZERO; deg];
        out.push(coeff);
        Self::from_vec(out)
    }

    pub fn evaluate(&self, point: F) -> F {
        let n = self.deg();
        let mut out = self.coeff[n];
        for i in (0..n).rev() {
            out *= point;
            out += self.coeff[i];
        }
        out
    }

    pub fn derivative(&self) -> Self {
        Self::from_vec(
            self.coeff
                .iter()
                .enumerate()
                .skip(1)
                .map(|(i, a)| F::from_u128(i as u128) * a)
                .collect(),
        )
    }

    // output 2x2 matrix R_0j by half-GCD, Figure 8.7 in The-Design-and-Analysis-of-Computer-Algorithms-Aho-Hopcroft.
    // fn half_gcd(f: &Poly<F>, g: &Poly<F>) -> ((Poly<F>, Poly<F>), (Poly<F>, Poly<F>))
    // {
    //     if 2*g.deg() <= f.deg() {
    //         return ((Self::one(), Self::zero()), (Self::zero(), Self::one()));
    //     }

    //     let m = f.deg() / 2;
    //     let f1 = f.slice(m);
    //     let g1 = g.slice(m);

    //     let mat1 = Self::half_gcd(&f1, &g1);
    //     let (d, e) = Self::mat_vec_mul(mat1.clone(), (f.clone(), g.clone()));

    //     let (q, r) = Self::euclidean(&d, &e);

    //     let e1 = e.slice(m/2);
    //     let r1 = r.slice(m/2);
    //     let mat2 = Self::half_gcd(&e1, &r1);

    //     let mat3 = ((Self::zero(), Self::one()), (Self::one(), -q));

    //     Self::mat_mat_mul(Self::mat_mat_mul(mat2, mat3), mat1)
    // }

    // output 2x2 matrix R_0j by half-GCD, (https://www.csd.uwo.ca/~mmorenom/CS424/Lectures/FastDivisionAndGcd.html/node6.html)
    fn half_gcd(a: &Poly<F>, b: &Poly<F>) -> PolyMat<F> {
        let m = Self::half_ceil(a.deg());
        if b.deg() <= m {
            return ((Self::one(), Self::zero()), (Self::zero(), Self::one()));
        }

        let a1 = a.slice(m);
        let b1 = b.slice(m);

        let m1 = Self::half_gcd(&a1, &b1);
        let (t, s) = Self::mat_vec_mul(m1.clone(), (a.clone(), b.clone()));

        if s.is_zero() {
            return m1;
        }

        let (q, r) = Self::euclidean(&t, &s);

        if r.is_zero() {
            let m2 = ((Self::zero(), Self::one()), (Self::one(), -q));
            return Self::mat_mat_mul(m2, m1);
        }

        let v = r.lead_coeff().invert().unwrap();
        let r_bar = r * &Self::constant(v);

        let m2 = (
            (Self::zero(), Self::one()),
            (Self::constant(v), q * &Self::constant(-v)),
        );
        let l = 2 * m - s.deg();
        let s1 = s.slice(l);
        // let r1 = r.slice(l) * &Self::constant(v);
        let r1 = r_bar.slice(l);

        let m3 = Self::half_gcd(&s1, &r1);

        Self::mat_mat_mul(Self::mat_mat_mul(m3, m2), m1)
    }

    fn half_ceil(a: usize) -> usize {
        a / 2 + a % 2
    }

    // output (q, r) such that f = q * g +r
    pub fn euclidean(f: &Poly<F>, g: &Poly<F>) -> PolyVec<F> {
        assert!(g.is_not_zero());

        let d = g.deg();
        let mut q = Self::zero();
        let mut r = f.clone();
        let g_lead_invert = g.coeff[d].invert().unwrap();

        while r.is_not_zero() && r.deg() >= d {
            let t = Self::monomial(r.deg() - d, r.lead_coeff() * g_lead_invert);
            q = q + &t;
            r = r + &(-t * g);
        }

        (q, r)
    }

    pub fn is_zero(&self) -> bool {
        for i in 0..self.coeff.len() {
            if self.coeff[i] != F::ZERO {
                return false;
            }
        }
        true
    }

    pub fn is_not_zero(&self) -> bool {
        !self.is_zero()
    }

    pub fn lead_coeff(&self) -> F {
        self.coeff[self.deg()]
    }

    // 2x2 matrix multiplication
    fn mat_mat_mul(a: PolyMat<F>, b: PolyMat<F>) -> PolyMat<F> {
        let first_row = (
            a.0 .0.clone() * &b.0 .0 + &(a.0 .1.clone() * &b.1 .0),
            a.0 .0 * &b.0 .1 + &(a.0 .1 * &b.1 .1),
        );
        let second_row = (
            a.1 .0.clone() * &b.0 .0 + &(a.1 .1.clone() * &b.1 .0),
            a.1 .0 * &b.0 .1 + &(a.1 .1 * &b.1 .1),
        );

        (first_row, second_row)
    }

    // 2x2 matrix * 2x1 vector multiplication
    fn mat_vec_mul(a: PolyMat<F>, b: PolyVec<F>) -> PolyVec<F> {
        (
            a.0 .0.clone() * &b.0 + &(a.0 .1.clone() * &b.1),
            a.1 .0 * &b.0 + &(a.1 .1 * &b.1),
        )
    }

    // slice polynomial into f such that input = f*x^m + g
    fn slice(&self, m: usize) -> Self {
        Self::from_vec(self.coeff[m..].to_vec())
    }

    // delete useless zero terms
    pub fn clear(&self) -> Self {
        Self::from_vec(self.coeff[0..self.deg() + 1].to_vec())
    }

    // given n-1 zeros of polynomial, find another zero.
    pub fn another_zero(&self, zeros: &[F]) -> F {
        let n = self.deg();
        assert_eq!(zeros.len(), n - 1);

        let q = zeros.iter().fold(self.clone(), |poly, &zero| {
            let (q, r) = Self::euclidean(&poly, &Self::from_vec(vec![-zero, F::ONE]));
            assert!(r.is_zero());
            q
        });
        -q.coeff[0]
    }
}

impl<'a, F: PrimeField> Add<&'a Poly<F>> for Poly<F> {
    type Output = Poly<F>;

    fn add(self, rhs: &'a Poly<F>) -> Poly<F> {
        let (mut longer, shorter): (Poly<F>, &Poly<F>);
        if self.coeff.len() > rhs.coeff.len() {
            (longer, shorter) = (self.clone(), &rhs);
        } else {
            (longer, shorter) = (rhs.clone(), &self);
        }

        for i in 0..shorter.coeff.len() {
            longer.coeff[i] += shorter.coeff[i];
        }

        longer
    }
}

// cleared version
// impl<'a, F: PrimeField> Mul<&'a Poly<F>> for Poly<F> {
//     type Output = Poly<F>;

//     fn mul(self, rhs: &'a Poly<F>) -> Poly<F>  {
//         let (l, r) = (self.clear(), rhs.clear());
//         let mut out = vec![F::ZERO; l.coeff.len() + r.coeff.len() - 1];
//         for i in 0..l.coeff.len() {
//             let tmp: Vec<F> = r.coeff.iter().zip(out.iter().skip(i)).map(|(&a, out_i)| a * l.coeff[i] + out_i).collect();
//             out.splice(i..i+r.coeff.len(), tmp);
//         }
//         Self::from_vec(out)
//     }
// }

// non-cleared version
impl<'a, F: PrimeField> Mul<&'a Poly<F>> for Poly<F> {
    type Output = Poly<F>;

    fn mul(self, rhs: &'a Poly<F>) -> Poly<F> {
        let mut out = vec![F::ZERO; self.coeff.len() + rhs.coeff.len() - 1];
        for i in 0..self.coeff.len() {
            let tmp: Vec<F> = rhs
                .coeff
                .iter()
                .zip(out.iter().skip(i))
                .map(|(&a, out_i)| a * self.coeff[i] + out_i)
                .collect();
            out.splice(i..i + rhs.coeff.len(), tmp);
        }
        Self::from_vec(out)
    }
}

impl<F: PrimeField> Neg for Poly<F> {
    type Output = Poly<F>;

    fn neg(self) -> Self::Output {
        let out: Vec<F> = self.coeff.iter().map(|&a| -a).collect();
        Self::from_vec(out)
    }
}

// function field element represented by a(x)-yb(x), how about Lagrange?
pub struct FunctionField<C: CurveAffine> {
    a: Poly<C::Base>,
    b: Poly<C::Base>,
}

#[allow(dead_code)]
impl<C: CurveAffine> FunctionField<C> {
    // line represented by y=\lambda x + \mu
    pub fn line(lambda: C::Base, mu: C::Base) -> Self {
        let a = Poly::from_vec(vec![mu, lambda]);
        let b = Poly::constant(C::Base::ONE);
        Self { a, b }
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
        if a > b {
            a
        } else {
            b
        }
    }

    // deg a, deg b, deg f
    fn deg_display(&self) -> (usize, usize, usize) {
        (self.a.deg(), self.b.deg(), self.deg())
    }

    // given points, output interpolation using Half-GCD.
    pub fn interpolate_mumford(points: &[C]) -> Self {
        let (u, v) = Self::mumford_repn(points);
        let (_, (c, b)) = Poly::half_gcd(&u, &v);
        let a = u * &c + &(v * &b);
        let out = Self { a: a.clear(), b };

        assert_eq!(out.deg(), points.len());
        out
    }

    // given semi-reduced distinct points, find mumford representation.
    fn mumford_repn(points: &[C]) -> (Poly<C::Base>, Poly<C::Base>) {
        let (px, py): (Vec<C::Base>, Vec<C::Base>) = points
            .iter()
            .map(|&p| {
                let coord = p.coordinates().unwrap();
                (*coord.x(), *coord.y())
            })
            .unzip();

        let v = lagrange_interpolate(&px, &py);

        let u = px.iter().fold(Poly::one(), |acc, &next| {
            acc * &Poly::from_vec(vec![-next, C::Base::ONE])
        });

        (u, Poly::from_vec(v))
    }

    // only for test. generate derivates for each time.
    pub fn evaluate_derivative(&self, point: C) -> C::Base {
        let coord = point.coordinates().unwrap();
        let (x, y) = (*coord.x(), *coord.y());

        let a_prime = self.a.derivative().evaluate(x);
        let b_prime = self.b.derivative().evaluate(x);

        let tmp = ((x + x + x) * x + C::a()) * (y + y).invert().unwrap();

        a_prime - tmp * self.b.evaluate(x) - y * b_prime
    }
}

#[allow(dead_code)]
// for test, random points P_i such that \sum P_i = O
pub fn random_points(rng: &mut ThreadRng, n: usize) -> Vec<Secp256k1Affine> {
    let mut points: Vec<Secp256k1Affine> = vec![];
    for _ in 0..n - 1 {
        points.push(Secp256k1Affine::random(rng.clone()));
    }
    let sum = points
        .iter()
        .skip(1)
        .fold(points[0], |acc, next| acc.add(next).to_affine());
    points.push(-sum);

    points
}

// Given integer, output ((v_j), (w_j)) such that num = \sum_{j=0} (v_j - w_j) (-3)^j. Both v_j and w_j cannot be one.
// pub fn minus_three_adic(num: i32) -> (Vec<bool>, Vec<bool>) {
//     todo!()
// }

#[cfg(test)]
mod test {
    use super::*;
    use halo2_proofs::halo2curves::group::Curve;
    use halo2_proofs::halo2curves::secp256k1::{Fp, Secp256k1Affine};
    use rand::thread_rng;
    use std::time::SystemTime;

    #[test]
    fn test_interpolate_mumford() {
        // generate P_i such that \sum P_i = O.
        let rng = &mut thread_rng();
        let points = random_points(rng, 45);

        // interpolate P_i
        let cur_time = SystemTime::now();
        let f = FunctionField::interpolate_mumford(&points);
        println!(
            "mumford interpolate in {}s",
            cur_time.elapsed().unwrap().as_secs()
        );
        println!("{:?}", f.deg_display());
        for i in 0..points.len() {
            assert!(f.is_zero_at(points[i]));
        }
    }
}
