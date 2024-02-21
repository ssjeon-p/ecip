use crate::utils::function_field::FunctionField;
use crate::utils::weil_reciprocity::*;
use halo2_common::halo2curves::CurveExt;
use halo2_proofs::circuit::AssignedCell;
use halo2_proofs::plonk::Expression;
use halo2_proofs::poly::Rotation;
use halo2_proofs::{
    arithmetic::Field,
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector},
};
use rand::thread_rng;

type ACell<F> = AssignedCell<F, F>;

// todo: enable to use different curve for zkp and ecip
#[derive(Debug, Clone)]
pub struct MSMConfig<C: CurveExt> {
    adv: [Column<Advice>; 4],

    s_pt: Selector,
    s_scalar: Selector,
    s_div: Selector,
    s_div_prime: Selector,
    s_final: Selector,

    clg: MSMChallenge<C>,
}

impl<C: CurveExt> MSMConfig<C> {
    pub fn configure(meta: &mut ConstraintSystem<C::Base>, n: usize) -> Self {
        let n = (n + n % 2) as i32;

        let adv = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];

        let s_pt = meta.selector();
        let s_scalar = meta.selector();
        let s_div = meta.selector();
        let s_div_prime = meta.selector();
        let s_final = meta.selector();

        meta.enable_equality(adv[2]);

        // todo: make challenge after commitment, not random
        let clg = MSMChallenge::from_higher(random_point::<C>());

        meta.create_gate("trace", |meta| {
            // adv = | x(P) | y(P) | trace(P) | trace(-P) |
            let [x, y, trace, trace_neg] = adv;
            let s_pt = meta.query_selector(s_pt);
            let lambda = Expression::Constant(clg.lambda);
            let mu = Expression::Constant(clg.mu);
            let x_one = Expression::Constant(to_x(clg.points[0]));

            vec![
                s_pt.clone()
                    * (trace.cur() * (mu.clone() + lambda.clone() * x.cur() - y.cur())
                        - x_one.clone()
                        + x.cur()),
                s_pt * (trace_neg.cur() * (mu + lambda * x.cur() + y.cur()) - x_one + x.cur()),
            ]
        });

        meta.create_gate("scalars", |meta| {
            // adv = | a_i | b_i | tr_acc | . |
            let [a, b, tr_acc, _] = adv;
            let s_scalar = meta.query_selector(s_scalar);
            // todo: for Tr(-Q) -n-1 => -n-2
            let trace = meta.query_advice(adv[2], Rotation(-n - 2));
            let trace_neg = meta.query_advice(adv[3], Rotation(-n - 2));

            vec![
                s_scalar * ((tr_acc.cur() - tr_acc.prev()) - a.cur() * trace - b.cur() * trace_neg),
            ]
        });

        meta.create_gate("ordinal evaluation", |meta| {
            // adv = | a_i | b_i | f_0 | f_2 |
            let [a, b, f_0, f_2] = adv;
            let s_div = meta.query_selector(s_div);

            let (x0, y0) = to_xy(clg.points[0]);
            let (x2, y2) = to_xy(clg.points[2]);

            let x0 = Expression::Constant(x0);
            let y0 = Expression::Constant(y0);
            let x2 = Expression::Constant(x2);
            let y2 = Expression::Constant(y2);

            let gate0 = f_0.prev() * x0 + a.cur() - y0 * b.cur() - f_0.cur();
            let gate2 = f_2.prev() * x2 + a.cur() - y2 * b.cur() - f_2.cur();

            vec![s_div.clone() * gate0, s_div * gate2]
        });

        meta.create_gate("derivative evaluation", |meta| {
            // adv = | a_i | b_i | f'_0 | f'_2 |
            let [a, b, f_0, f_2] = adv;
            let s_div_prime = meta.query_selector(s_div_prime);

            let (x0, y0) = to_xy(clg.points[0]);
            let (x2, y2) = to_xy(clg.points[2]);

            let x0 = Expression::Constant(x0);
            let y0 = Expression::Constant(y0);
            let x2 = Expression::Constant(x2);
            let y2 = Expression::Constant(y2);
            let d0 = Expression::Constant(clg.dx_dy[0]);
            let d2 = Expression::Constant(clg.dx_dy[2]);

            let b_ord = meta.query_advice(b, Rotation(-n / 2 - 3));

            let gate0 = f_0.prev() * x0 + a.cur() - y0 * b.cur() - f_0.cur() - d0 * b_ord.clone();
            let gate2 = f_2.prev() * x2 + a.cur() - y2 * b.cur() - f_2.cur() - d2 * b_ord;

            vec![s_div_prime.clone() * gate0, s_div_prime * gate2]
        });

        meta.create_gate("final gate", |meta| {
            // |  |  |    f_0    |    f_2   |
            // |  |  |     .     |     .    |
            // |  |  |     .     |     .    |
            // |  |  |     .     |     .    |
            // |  |  |    f'_0   |   f'_2   |
            // |  |  |  f_0 _inv |  f_2_inv |  cur
            // |  |  |   tr_z    |    .     |
            // |  |  |  tr_prev  |    .     |
            // |  |  |  tr_acc   |    .     |
            let f_0_eval = meta.query_advice(adv[2], Rotation(-n / 2 - 4));
            let f_2_eval = meta.query_advice(adv[3], Rotation(-n / 2 - 4));
            let f_0_inv = meta.query_advice(adv[2], Rotation::cur());
            let f_2_inv = meta.query_advice(adv[3], Rotation::cur());
            let f_prime_0 = meta.query_advice(adv[2], Rotation::prev());
            let f_prime_2 = meta.query_advice(adv[3], Rotation::prev());
            let tr_z = meta.query_advice(adv[2], Rotation::next());
            let tr_prev = meta.query_advice(adv[2], Rotation(2));
            let tr_acc = meta.query_advice(adv[2], Rotation(3));
            let c2 = clg.higher_c2();
            let c2lam = Expression::Constant(c2 + clg.lambda + clg.lambda);
            let c2 = Expression::Constant(c2);
            let one = Expression::Constant(C::Base::ONE);
            let s_final = meta.query_selector(s_final);

            vec![
                s_final.clone()
                    * (tr_z.clone() + f_prime_0 * f_0_inv.clone() * c2lam
                        - f_prime_2 * f_2_inv.clone() * c2),
                s_final.clone() * (tr_acc + tr_prev.clone() + tr_prev.clone() + tr_prev - tr_z),
                s_final.clone() * (f_0_eval * f_0_inv - one.clone()),
                s_final * (f_2_eval * f_2_inv - one),
            ]
        });

        Self {
            adv,
            s_pt,
            s_scalar,
            s_div,
            s_div_prime,
            s_final,
            clg,
        }
    }
}

#[derive(Debug, Clone)]
pub struct MSMChip<C: CurveExt> {
    config: MSMConfig<C>,
    n: usize,
}

impl<C: CurveExt> MSMChip<C> {
    pub fn new(config: MSMConfig<C>, n: usize) -> Self {
        Self {
            config,
            n: n + n % 2,
        }
    }
    fn assign_points(
        &self,
        mut layouter: impl Layouter<C::Base>,
        points: &[C],
        scalars: &[(C::Base, C::Base)],
    ) -> Result<ACell<C::Base>, Error> {
        let n = self.n;
        layouter.assign_region(
            || "ec points and trace",
            |mut region| {
                let mut trace = vec![];
                let mut trace_neg = vec![];
                for (offset, pt) in points.iter().enumerate() {
                    self.config.s_pt.enable(&mut region, offset)?;
                    let (x, y) = to_xy(*pt);
                    region.assign_advice(
                        || "x_i",
                        self.config.adv[0],
                        offset,
                        || Value::known(x),
                    )?;
                    region.assign_advice(
                        || "y_i",
                        self.config.adv[1],
                        offset,
                        || Value::known(y),
                    )?;

                    trace.push(region.assign_advice(
                        || "trace",
                        self.config.adv[2],
                        offset,
                        || Value::known(trace_higher(points[offset], &self.config.clg)),
                    )?);
                    trace_neg.push(region.assign_advice(
                        || "trace",
                        self.config.adv[3],
                        offset,
                        || Value::known(trace_higher(-points[offset], &self.config.clg)),
                    )?);
                }

                let mut acc = region.assign_advice(
                    || "init acc",
                    self.config.adv[2],
                    n + 1,
                    || Value::known(C::Base::ZERO),
                )?;

                for (offset, i) in (n + 2..=2 * n + 2).zip(0..=n) {
                    self.config.s_scalar.enable(&mut region, offset)?;
                    region.assign_advice(
                        || "scalar a",
                        self.config.adv[0],
                        offset,
                        || Value::known(scalars[i].0),
                    )?;
                    region.assign_advice(
                        || "scalar b",
                        self.config.adv[1],
                        offset,
                        || Value::known(scalars[i].1),
                    )?;
                    acc = region.assign_advice(
                        || "trace_acc",
                        self.config.adv[2],
                        offset,
                        || {
                            acc.value().copied()
                                + Value::known(scalars[i].0) * trace[i].value().copied()
                                + Value::known(scalars[i].1) * trace_neg[i].value().copied()
                        },
                    )?;
                }
                Ok(acc)
            },
        )
    }

    fn assign_zero(&self, mut layouter: impl Layouter<C::Base>) -> Result<ACell<C::Base>, Error> {
        layouter.assign_region(
            || "assign zero",
            |mut region| {
                let zero = region.assign_advice(
                    || "zero",
                    self.config.adv[2],
                    0,
                    || Value::known(C::Base::ZERO),
                )?;
                Ok(zero)
            },
        )
    }

    fn assign_divisors(
        &self,
        mut layouter: impl Layouter<C::Base>,
        f: &FunctionField<C::Base, C>,
        tr_prev: ACell<C::Base>,
        tr_last: Option<ACell<C::Base>>,
    ) -> Result<ACell<C::Base>, Error> {
        layouter.assign_region(
            || "divisor witness",
            |mut region| {
                // max degree of divisor = (num of points + 4) / 2
                let deg = self.n / 2 + 2;

                let (x0, y0) = to_xy(self.config.clg.points[0]);
                let (x2, y2) = to_xy(self.config.clg.points[2]);
                let (d0, d2) = (self.config.clg.dx_dy[0], self.config.clg.dx_dy[2]);

                let c2 = Value::known(self.config.clg.higher_c2());
                let lambda = Value::known(self.config.clg.lambda);
                let c2lam = c2 + lambda + lambda;

                let f_a: Vec<C::Base> = (0..=deg)
                    .map(|i| *f.a.coeff.get(i).unwrap_or(&C::Base::ZERO))
                    .collect();
                let f_b: Vec<C::Base> = (0..=deg)
                    .map(|i| *f.b.coeff.get(i).unwrap_or(&C::Base::ZERO))
                    .collect();

                let mut f_0 = Value::known(C::Base::ZERO);
                let mut f_2 = Value::known(C::Base::ZERO);

                region.assign_advice(|| "init f_1", self.config.adv[2], 0, || f_0)?;
                region.assign_advice(|| "init f_2", self.config.adv[3], 0, || f_2)?;

                for (offset, i) in (1..=deg + 1).zip((0..=deg).rev()) {
                    self.config.s_div.enable(&mut region, offset)?;
                    let a = region.assign_advice(
                        || "a_i",
                        self.config.adv[0],
                        offset,
                        || Value::known(f_a[i]),
                    )?;
                    let b = region.assign_advice(
                        || "b_i",
                        self.config.adv[1],
                        offset,
                        || Value::known(f_b[i]),
                    )?;
                    f_0 = f_0 * Value::known(x0) + a.value().copied()
                        - Value::known(y0) * b.value().copied();
                    f_2 = f_2 * Value::known(x2) + a.value().copied()
                        - Value::known(y2) * b.value().copied();
                    region.assign_advice(|| "f_0", self.config.adv[2], offset, || f_0)?;
                    region.assign_advice(|| "f_2", self.config.adv[3], offset, || f_2)?;
                }

                let mut f_prime_0 = Value::known(C::Base::ZERO);
                let mut f_prime_2 = Value::known(C::Base::ZERO);
                region.assign_advice(|| "init f_p_0", self.config.adv[2], deg + 2, || f_prime_0)?;
                region.assign_advice(|| "init f_p_2", self.config.adv[3], deg + 2, || f_prime_2)?;

                // derivative of divisor witness
                for (offset, i) in (deg + 3..=2 * deg + 2).zip((1..=deg).rev()) {
                    self.config.s_div_prime.enable(&mut region, offset)?;
                    let a_p = region.assign_advice(
                        || "a_p_i",
                        self.config.adv[0],
                        offset,
                        || Value::known(f_a[i] * C::Base::from(i as u64)),
                    )?;
                    let b_p = region.assign_advice(
                        || "b_p_i",
                        self.config.adv[1],
                        offset,
                        || Value::known(f_b[i] * C::Base::from(i as u64)),
                    )?;
                    f_prime_0 = f_prime_0 * Value::known(x0) + a_p.value().copied()
                        - Value::known(y0) * b_p.value().copied()
                        - Value::known(d0 * f_b[i - 1]);
                    f_prime_2 = f_prime_2 * Value::known(x2) + a_p.value().copied()
                        - Value::known(y2) * b_p.value().copied()
                        - Value::known(d2 * f_b[i - 1]);
                    region.assign_advice(|| "f_p_0", self.config.adv[2], offset, || f_prime_0)?;
                    region.assign_advice(|| "f_p_2", self.config.adv[3], offset, || f_prime_2)?;
                }

                self.config.s_final.enable(&mut region, 2 * deg + 3)?;
                let f_0_inv = f_0.map(|t| t.invert().unwrap());
                let f_2_inv = f_2.map(|t| t.invert().unwrap());
                region.assign_advice(|| "f_0_inv", self.config.adv[2], 2 * deg + 3, || f_0_inv)?;
                region.assign_advice(|| "f_2_inv", self.config.adv[3], 2 * deg + 3, || f_2_inv)?;
                let tr_z = c2 * f_prime_2 * f_2_inv - c2lam * f_prime_0 * f_0_inv;
                let tr_z =
                    region.assign_advice(|| "trace_z", self.config.adv[2], 2 * deg + 4, || tr_z)?;

                tr_prev.copy_advice(
                    || "previous trace",
                    &mut region,
                    self.config.adv[2],
                    2 * deg + 5,
                )?;
                let prev = tr_prev.value().copied();
                let tr_acc = match &tr_last {
                    None => region.assign_advice(
                        || "accumulate trace",
                        self.config.adv[2],
                        2 * deg + 6,
                        || -prev - prev - prev + tr_z.value(),
                    )?,
                    Some(tr) => region.assign_advice(
                        || "for the last divisor witness",
                        self.config.adv[2],
                        2 * deg + 6,
                        || tr.value().copied(),
                    )?,
                };

                Ok(tr_acc)
            },
        )
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

// for test
fn random_point<C: CurveExt>() -> C {
    let rng = &mut thread_rng();
    let mut x;
    let out;
    loop {
        x = C::Base::random(rng.clone());
        let y_sqr = x.cube() + C::a() * x + C::b();
        let y: Option<C::Base> = y_sqr.sqrt().into();
        if let Some(v) = y {
            out = v;
            break;
        }
    }
    C::new_jacobian(x, out, C::Base::ONE).unwrap()
}

struct MSMCircuit<C: CurveExt, const N: usize> {
    points: Vec<C>,
    scalars: Vec<(C::Base, C::Base)>,
    divisor_witness: Vec<FunctionField<C::Base, C>>,
}

impl<C: CurveExt, const N: usize> Circuit<C::Base> for MSMCircuit<C, N> {
    type Config = MSMConfig<C>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            points: vec![C::identity(); N],
            scalars: vec![(C::Base::ZERO, C::Base::ZERO); N],
            divisor_witness: vec![FunctionField::identity()],
        }
    }

    fn configure(meta: &mut ConstraintSystem<C::Base>) -> Self::Config {
        MSMConfig::configure(meta, N)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Base>,
    ) -> Result<(), Error> {
        let chip = MSMChip::new(config, N);
        let tr = chip.assign_points(
            layouter.namespace(|| "assign points"),
            &self.points,
            &self.scalars,
        )?;
        let mut tr_acc = chip.assign_zero(layouter.namespace(|| "zero"))?;
        for f in self.divisor_witness.iter().skip(1).rev() {
            tr_acc =
                chip.assign_divisors(layouter.namespace(|| "assign divisor"), f, tr_acc, None)?;
        }
        chip.assign_divisors(
            layouter.namespace(|| "last witness"),
            &self.divisor_witness[0],
            tr_acc,
            Some(tr),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::utils::function_field::*;
    use halo2_common::{
        halo2curves::{bn256::Bn256, grumpkin::Fq},
        transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer},
    };
    use halo2_liam_eagen_msm::regular_functions_utils::Grumpkin;
    use halo2_proofs::{
        dev::MockProver,
        plonk::{create_proof, keygen_pk, keygen_vk, verify_proof},
        poly::{
            commitment::ParamsProver,
            kzg::{
                commitment::{KZGCommitmentScheme, ParamsKZG},
                multiopen::{ProverGWC, ProverSHPLONK, VerifierSHPLONK},
                strategy::{self, SingleStrategy},
            },
        },
    };
    use rand::rngs::OsRng;
    use std::time::SystemTime;

    use super::*;
    #[test]
    fn test_ecip_circuit() {
        let l: u32 = 161; // |scalar| < 3^l < q, where F_q is scalar field. For 256 bit scalar field, l <= 161
        const N: usize = 10000;
        // we need 2N + l * (N + 10) rows and few more
        let row = 2 * N + l as usize * (N + 10);
        let mut k = 0;
        while (1 << k) < row {
            k += 1;
        }

        println!("The number of points = {}", N);
        println!("Scalars are less than 3^{}", l);
        println!("rows k = {}", k);

        let rng = &mut thread_rng();
        let mut points = random_points(rng, N);
        let mut scalars_int: Vec<isize> = vec![];
        let mut scalars: Vec<(Fq, Fq)> = vec![];
        for i in 0..N {
            scalars_int.push(rand::random::<isize>() % -(3isize.pow(l)));
            let (a, b) = split_num(scalars_int[i]);
            scalars.push((into_field(a), into_field(b)));
        }
        scalars.push((Fq::ONE, Fq::ZERO));
        let cur_time = SystemTime::now();
        let (divisor_witness, prod) = FunctionField::ecip_interpolate_lev(&scalars_int, &points);
        points.push(-prod);
        // if you put wrong point, then fail
        // points[N] = G1Affine::random(rng);
        println!(
            "prepare divisor witness in {}ms",
            cur_time.elapsed().unwrap().as_millis()
        );

        let circuit = MSMCircuit::<Grumpkin, N> {
            points,
            scalars,
            divisor_witness,
        };

        let params: ParamsKZG<Bn256> = ParamsKZG::setup(3, OsRng);
        let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

        let proof = create_proof::<KZGCommitmentScheme<_>, ProverSHPLONK<_>, _, _, _, _>(
            &params,
            &pk,
            &[circuit],
            &[],
            OsRng,
            &mut transcript,
        )
        .expect("proof generation should not fail");

        // let v = verify_proof(&params, &vk, SingleStrategy::new(&params), &[], &mut transcript);
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_circuit() {
        // cargo test --all-features -- --nocapture plot_circuit
        use plotters::prelude::*;

        let root = BitMapBackend::new("layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Layout", ("sans-serif", 60)).unwrap();

        let k = 8;
        let rng = &mut thread_rng();
        const N: usize = 100;
        let points = random_points_sum_zero(rng, N);
        let f = FunctionField::interpolate_incremental(&points);
        let circuit = MSMCircuit::<G1Affine, N> {
            points,
            divisor_witness: f,
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(k, &circuit, &root)
            .unwrap();
    }
}
