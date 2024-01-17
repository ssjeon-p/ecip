use halo2_proofs::halo2curves::ff::PrimeField;
use std::cmp::max;
use std::ops::{Add, Mul, Neg, Sub};
use std::vec;

use super::function_field::field_scalar_mul;

#[derive(Clone, Debug, PartialEq, Default)]
pub struct Poly<F: PrimeField> {
    pub coeff: Vec<F>,
}

type PolyMat<F> = ((Poly<F>, Poly<F>), (Poly<F>, Poly<F>));

impl<F: PrimeField> Poly<F> {
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

    pub fn vertical_line(x: F) -> Self {
        Self {
            coeff: vec![-x, F::ONE],
        }
    }

    pub fn constant(value: F) -> Self {
        Self { coeff: vec![value] }
    }

    // output coeff * x^deg
    pub fn monomial(deg: usize, coeff: F) -> Self {
        let mut out = vec![F::ZERO; deg];
        out.push(coeff);
        Self { coeff: out }
    }

    pub fn evaluate(&self, point: F) -> F {
        if self.coeff.is_empty() {
            return F::ZERO;
        }
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
                .map(|(i, &a)| field_scalar_mul(i as isize, a))
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
    pub fn half_gcd(a: &Poly<F>, b: &Poly<F>) -> PolyMat<F> {
        let m = Self::half_ceil(a.deg());
        if b.deg() <= m {
            return ((Self::one(), Self::zero()), (Self::zero(), Self::one()));
        }

        let a1 = a.slice(m);
        let b1 = b.slice(m);

        let m1 = Self::half_gcd(&a1, &b1);
        let (t, s) = Self::mat_vec_mul(&m1, a, b);

        if s.is_zero() {
            return m1;
        }

        let (q, r) = Self::euclidean(&t, &s);

        if r.is_zero() {
            let m2 = ((Self::zero(), Self::one()), (Self::one(), -q));
            return Self::mat_mat_mul(&m2, &m1);
        }

        let v = r.lead_coeff().invert().unwrap();
        let r_bar = r * Self::constant(v);

        let m2 = (
            (Self::zero(), Self::one()),
            (Self::constant(v), q * Self::constant(-v)),
        );
        let l = 2 * m - s.deg();
        let s1 = s.slice(l);
        // let r1 = r.slice(l) * Self::constant(v);
        let r1 = r_bar.slice(l);

        let m3 = Self::half_gcd(&s1, &r1);

        Self::mat_mat_mul(&Self::mat_mat_mul(&m3, &m2), &m1)
    }

    fn half_ceil(a: usize) -> usize {
        a / 2 + a % 2
    }

    // output (q, r) such that f = q * g +r
    pub fn euclidean(f: &Poly<F>, g: &Poly<F>) -> (Poly<F>, Poly<F>) {
        assert!(g.is_not_zero());

        let d = g.deg();
        let mut q = Self::zero();
        let mut r = f.clone();
        let g_lead_invert = g.coeff[d].invert().unwrap();

        while r.is_not_zero() && r.deg() >= d {
            let t = &Self::monomial(r.deg() - d, r.lead_coeff() * g_lead_invert);
            q = q + t;
            r = r - t * g;
            // todo: efficient?
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
    fn mat_mat_mul(a: &PolyMat<F>, b: &PolyMat<F>) -> PolyMat<F> {
        let first_row = (
            &a.0 .0 * &b.0 .0 + &a.0 .1 * &b.1 .0,
            &a.0 .0 * &b.0 .1 + &a.0 .1 * &b.1 .1,
        );
        let second_row = (
            &a.1 .0 * &b.0 .0 + &a.1 .1 * &b.1 .0,
            &a.1 .0 * &b.0 .1 + &a.1 .1 * &b.1 .1,
        );

        (first_row, second_row)
    }

    // 2x2 matrix * 2x1 vector multiplication
    fn mat_vec_mul(a: &PolyMat<F>, b0: &Poly<F>, b1: &Poly<F>) -> (Poly<F>, Poly<F>) {
        (&a.0 .0 * b0 + &a.0 .1 * b1, &a.1 .0 * b0 + &a.1 .1 * b1)
    }

    // slice polynomial into f such that input = f*x^m + g
    fn slice(&self, m: usize) -> Self {
        Self::from_vec(self.coeff[m..].to_vec())
    }

    // delete useless zero terms
    pub fn clear(&mut self) {
        self.coeff.truncate(self.deg() + 1);
    }

    // given n-1 zeros of polynomial, find another zero.
    pub fn another_zero(&self, zeros: &[F]) -> F {
        let n = self.deg();
        assert_eq!(zeros.len(), n - 1);

        let sum = -self.coeff[n - 1] * self.coeff[n].invert().unwrap();

        zeros.iter().fold(sum, |acc, next| acc - next)
    }
}

impl<'a, 'b, F: PrimeField> Add<&'b Poly<F>> for &'a Poly<F> {
    type Output = Poly<F>;

    fn add(self, rhs: &'b Poly<F>) -> Poly<F> {
        let n = max(self.coeff.len(), rhs.coeff.len());
        let mut out = vec![];
        for i in 0..n {
            let (a, b) = (self.coeff.get(i), rhs.coeff.get(i));
            match (a, b) {
                (Some(a), Some(b)) => {
                    out.push(*a + *b);
                }
                (Some(a), None) => {
                    out.push(*a);
                }
                (None, Some(b)) => {
                    out.push(*b);
                }
                _ => {
                    panic!();
                }
            }
        }
        Poly { coeff: out }
    }
}

impl<'a, 'b, F: PrimeField> Sub<&'b Poly<F>> for &'a Poly<F> {
    type Output = Poly<F>;

    fn sub(self, rhs: &'b Poly<F>) -> Poly<F> {
        let n = max(self.coeff.len(), rhs.coeff.len());
        let mut out = vec![];
        for i in 0..n {
            let (a, b) = (self.coeff.get(i), rhs.coeff.get(i));
            match (a, b) {
                (Some(a), Some(b)) => {
                    out.push(*a - *b);
                }
                (Some(a), None) => {
                    out.push(*a);
                }
                (None, Some(b)) => {
                    out.push(-*b);
                }
                _ => {
                    panic!();
                }
            }
        }
        Poly { coeff: out }
    }
}

impl<'a, 'b, F: PrimeField> Mul<&'b Poly<F>> for &'a Poly<F> {
    type Output = Poly<F>;

    fn mul(self, rhs: &'b Poly<F>) -> Poly<F> {
        let l_len = self.deg() + 1;
        let r_len = rhs.deg() + 1;
        let mut out = vec![F::ZERO; l_len + r_len - 1];
        for i in 0..l_len {
            let tmp: Vec<F> = rhs
                .coeff
                .iter()
                .zip(out.iter().skip(i))
                .map(|(&a, out_i)| a * self.coeff[i] + out_i)
                .collect();
            out.splice(i..i + r_len, tmp);
        }
        Poly { coeff: out }
    }
}

impl<'a, F: PrimeField> Neg for &'a Poly<F> {
    type Output = Poly<F>;

    fn neg(self) -> Poly<F> {
        let out: Vec<F> = self.coeff.iter().map(|&a| -a).collect();
        Poly { coeff: out }
    }
}


// without references
impl<'b, F: PrimeField> Add<&'b Poly<F>> for Poly<F> {
    type Output = Poly<F>;

    fn add(self, rhs: &'b Poly<F>) -> Poly<F> {
        &self + rhs
    }
}

impl<'a, F: PrimeField> Add<Poly<F>> for &'a Poly<F> {
    type Output = Poly<F>;

    fn add(self, rhs: Poly<F>) -> Poly<F> {
        self + &rhs
    }
}

impl<F: PrimeField> Add<Poly<F>> for Poly<F> {
    type Output = Poly<F>;

    fn add(self, rhs: Poly<F>) -> Poly<F> {
        &self + &rhs
    }
}

impl<'b, F: PrimeField> Sub<&'b Poly<F>> for Poly<F> {
    type Output = Poly<F>;

    fn sub(self, rhs: &'b Poly<F>) -> Poly<F> {
        &self - rhs
    }
}

impl<'a, F: PrimeField> Sub<Poly<F>> for &'a Poly<F> {
    type Output = Poly<F>;

    fn sub(self, rhs: Poly<F>) -> Poly<F> {
        self - &rhs
    }
}

impl<F: PrimeField> Sub<Poly<F>> for Poly<F> {
    type Output = Poly<F>;

    fn sub(self, rhs: Poly<F>) -> Poly<F> {
        &self - &rhs
    }
}

impl<'b, F: PrimeField> Mul<&'b Poly<F>> for Poly<F> {
    type Output = Poly<F>;

    fn mul(self, rhs: &'b Poly<F>) -> Poly<F> {
        &self * rhs
    }
}

impl<'a, F: PrimeField> Mul<Poly<F>> for &'a Poly<F> {
    type Output = Poly<F>;

    fn mul(self, rhs: Poly<F>) -> Poly<F> {
        self * &rhs
    }
}

impl<F: PrimeField> Mul<Poly<F>> for Poly<F> {
    type Output = Poly<F>;

    fn mul(self, rhs: Poly<F>) -> Poly<F> {
        &self * &rhs
    }
}

impl<F: PrimeField> Neg for Poly<F> {
    type Output = Poly<F>;

    fn neg(self) -> Poly<F> {
        -&self
    }
}
