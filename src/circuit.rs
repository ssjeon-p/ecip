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

// todo: enable to use different curve for zkp and ecip
#[derive(Debug, Clone)]
pub struct MSMConfig<C: CurveExt> {
    adv: [Column<Advice>; 4],

    s_pt: Selector,
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
        let s_div = meta.selector();
        let s_div_prime = meta.selector();
        let s_final = meta.selector();

        meta.enable_equality(adv[2]);

        // todo: make challenge after commitment, not random
        let clg = MSMChallenge::from_higher(random_point::<C>());

        meta.create_gate("trace", |meta| {
            // adv = | x(P) | y(P) | trace | . |
            let [x, y, trace, _] = adv;
            let s_pt = meta.query_selector(s_pt);
            let lambda = Expression::Constant(clg.lambda);
            let mu = Expression::Constant(clg.mu);
            let x_one = Expression::Constant(to_x(clg.points[0]));

            vec![
                s_pt * ((trace.cur() - trace.prev()) * (mu + lambda * x.cur() - y.cur()) - x_one
                    + x.cur()),
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

            let b_ord = meta.query_advice(b, Rotation(-n / 2 - 1));

            let gate0 = f_0.prev() * x0 + a.cur() - y0 * b.cur() - f_0.cur() - d0 * b_ord.clone();
            let gate2 = f_2.prev() * x2 + a.cur() - y2 * b.cur() - f_2.cur() - d2 * b_ord;

            vec![s_div_prime.clone() * gate0, s_div_prime * gate2]
        });

        meta.create_gate("final gate", |meta| {
            let f_0_eval = meta.query_advice(adv[2], Rotation(-n / 2 - 2));
            let f_2_eval = meta.query_advice(adv[3], Rotation(-n / 2 - 2));
            let f_0_inv = meta.query_advice(adv[2], Rotation::cur());
            let f_2_inv = meta.query_advice(adv[3], Rotation::cur());
            let f_prime_0 = meta.query_advice(adv[2], Rotation::prev());
            let f_prime_2 = meta.query_advice(adv[3], Rotation::prev());
            let trace = meta.query_advice(adv[2], Rotation::next());
            let c2 = clg.higher_c2();
            let c2lam = Expression::Constant(c2 + clg.lambda + clg.lambda);
            let c2 = Expression::Constant(c2);
            let one = Expression::Constant(C::Base::ONE);
            let s_final = meta.query_selector(s_final);

            vec![
                s_final.clone()
                    * (trace + f_prime_0 * f_0_inv.clone() * c2lam
                        - f_prime_2 * f_2_inv.clone() * c2),
                s_final.clone() * (f_0_eval * f_0_inv - one.clone()),
                s_final * (f_2_eval * f_2_inv - one),
            ]
        });

        Self {
            adv,
            s_pt,
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
    ) -> Result<AssignedCell<C::Base, C::Base>, Error> {
        // With invalid witness, circuit should panic at final gate.
        // let mut points = points.to_vec();
        // points[0] = random_point();
        layouter.assign_region(
            || "ec points and trace",
            |mut region| {
                let mut trace = region.assign_advice(
                    || "init trace",
                    self.config.adv[2],
                    0,
                    || Value::known(C::Base::ZERO),
                )?;
                for (offset, pt) in points.iter().enumerate() {
                    self.config.s_pt.enable(&mut region, offset + 1)?;
                    let (x, y) = to_xy(*pt);
                    region.assign_advice(
                        || "x_i",
                        self.config.adv[0],
                        offset + 1,
                        || Value::known(x),
                    )?;
                    region.assign_advice(
                        || "y_i",
                        self.config.adv[1],
                        offset + 1,
                        || Value::known(y),
                    )?;
                    let tr = trace_higher(points[offset], &self.config.clg);
                    trace = region.assign_advice(
                        || "trace",
                        self.config.adv[2],
                        offset + 1,
                        || Value::known(tr) + trace.value().copied(),
                    )?;
                }
                Ok(trace)
            },
        )
    }

    fn assign_divisor(
        &self,
        mut layouter: impl Layouter<C::Base>,
        f: &FunctionField<C::Base, C>,
        trace: AssignedCell<C::Base, C::Base>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "divisor witness",
            |mut region| {
                let deg = self.n / 2;
                let f_a: Vec<C::Base> = (0..=deg)
                    .map(|i| *f.a.coeff.get(i).unwrap_or(&C::Base::ZERO))
                    .collect();
                let f_b: Vec<C::Base> = (0..=deg)
                    .map(|i| *f.b.coeff.get(i).unwrap_or(&C::Base::ZERO))
                    .collect();

                let (x0, y0) = to_xy(self.config.clg.points[0]);
                let (x2, y2) = to_xy(self.config.clg.points[2]);
                let (d0, d2) = (self.config.clg.dx_dy[0], self.config.clg.dx_dy[2]);

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
                trace.copy_advice(|| "trace", &mut region, self.config.adv[2], 2 * deg + 4)?;

                Ok(())
            },
        )
    }
}

fn to_xy<C: CurveExt>(pt: C) -> (C::Base, C::Base) {
    let (x, y, z) = pt.jacobian_coordinates();
    let z_inv = z.invert().unwrap();
    let z_inv_sq = z_inv * z_inv;
    (x * z_inv_sq, y * z_inv_sq * z_inv)
}

fn to_x<C: CurveExt>(pt: C) -> C::Base {
    let (x, _, z) = pt.jacobian_coordinates();
    let z_inv = z.invert().unwrap();
    x * z_inv * z_inv
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
    divisor_witness: FunctionField<C::Base, C>,
}

impl<C: CurveExt, const N: usize> Circuit<C::Base> for MSMCircuit<C, N> {
    type Config = MSMConfig<C>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            points: vec![C::identity(); N],
            divisor_witness: FunctionField::identity(),
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
        let tr = chip.assign_points(layouter.namespace(|| "assign points"), &self.points)?;
        chip.assign_divisor(
            layouter.namespace(|| "assign divisor"),
            &self.divisor_witness,
            tr,
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::utils::function_field::*;
    use halo2_liam_eagen_msm::regular_functions_utils::Grumpkin;
    use halo2_proofs::dev::MockProver;
    use std::time::SystemTime;

    use super::*;
    #[test]
    fn test_circuit() {
        let k = 10;
        let rng = &mut thread_rng();
        const N: usize = 200;
        let points = random_points_sum_zero(rng, N);
        let cur_time = SystemTime::now();
        let f = FunctionField::interpolate_lev(&points);
        println!(
            "prepare divisor witness in {}ms",
            cur_time.elapsed().unwrap().as_millis()
        );
        let circuit = MSMCircuit::<Grumpkin, N> {
            points,
            divisor_witness: f,
        };
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
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
