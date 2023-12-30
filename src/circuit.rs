use crate::utils::weil_reciprocity::*;
use halo2_proofs::circuit::AssignedCell;
use halo2_proofs::plonk::Expression;
use halo2_proofs::poly::Rotation;
use halo2_proofs::{
    arithmetic::Field,
    circuit::{Layouter, SimpleFloorPlanner, Value},
    halo2curves::CurveAffine,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector},
};
use rand::thread_rng;

pub struct AssignedPoint<C: CurveAffine>(
    AssignedCell<C::Base, C::Base>,
    AssignedCell<C::Base, C::Base>,
);
#[allow(dead_code)]
pub struct AssignedPair<C: CurveAffine> {
    point: AssignedPoint<C>,
    trace: AssignedCell<C::Base, C::Base>,
}

// todo: enable to use different curve for zkp and ecip
#[derive(Debug, Clone)]
pub struct MSMConfig<C: CurveAffine> {
    point: (Column<Advice>, Column<Advice>),
    trace: Column<Advice>,
    prev_tr_copy: Column<Advice>,
    s_pt: Selector,
    clg: MSMChallenge<C>,
}

impl<C: CurveAffine> MSMConfig<C> {
    pub fn configure(meta: &mut ConstraintSystem<C::Base>) -> Self {
        let s_pt = meta.selector();
        let pt_x = meta.advice_column();
        let pt_y = meta.advice_column();
        let trace = meta.advice_column();
        let prev_tr_copy = meta.advice_column();
        // todo: make challenge independent of commitment, not random
        let clg = MSMChallenge::from_simple((random_point(), random_point()));

        meta.enable_equality(prev_tr_copy);
        meta.enable_equality(trace);

        meta.create_gate("trace", |meta| {
            let s_pt = meta.query_selector(s_pt);
            let x = meta.query_advice(pt_x, Rotation::cur());
            let y = meta.query_advice(pt_y, Rotation::cur());
            let tr = meta.query_advice(trace, Rotation::cur());
            let prev_tr = meta.query_advice(prev_tr_copy, Rotation::cur());
            let one = Expression::Constant(C::Base::ONE);
            let lambda = Expression::Constant(clg.lambda);
            let mu = Expression::Constant(clg.mu);

            vec![s_pt * ((tr - prev_tr) * (mu + lambda * x - y) - one)]
        });

        Self {
            point: (pt_x, pt_y),
            trace,
            prev_tr_copy,
            s_pt,
            clg,
        }
    }
}

#[derive(Debug, Clone)]
pub struct MSMChip<C: CurveAffine> {
    config: MSMConfig<C>,
}

impl<C: CurveAffine> MSMChip<C> {
    pub fn new(config: MSMConfig<C>) -> Self {
        Self { config }
    }

    fn assign_first_row(
        &self,
        mut layouter: impl Layouter<C::Base>,
    ) -> Result<AssignedPair<C>, Error> {
        layouter.assign_region(
            || "first row with zeros",
            |mut region| {
                let x = region.assign_advice(
                    || "x_i",
                    self.config.point.0,
                    0,
                    || Value::known(C::Base::ZERO),
                )?;
                let y = region.assign_advice(
                    || "y_i",
                    self.config.point.1,
                    0,
                    || Value::known(C::Base::ZERO),
                )?;
                let trace = region.assign_advice(
                    || "trace",
                    self.config.trace,
                    0,
                    || Value::known(C::Base::ZERO),
                )?;
                region.assign_advice(
                    || "copied trace",
                    self.config.prev_tr_copy,
                    0,
                    || Value::known(C::Base::ZERO),
                )?;
                Ok(AssignedPair {
                    point: AssignedPoint(x, y),
                    trace,
                })
            },
        )
    }
    fn assign_point(
        &self,
        mut layouter: impl Layouter<C::Base>,
        prev_tr: &AssignedCell<C::Base, C::Base>,
        point: &C,
    ) -> Result<AssignedPair<C>, Error> {
        layouter.assign_region(
            || "ec points and trace",
            |mut region| {
                self.config.s_pt.enable(&mut region, 0)?;
                let pt = point.coordinates().unwrap();
                let x = region.assign_advice(
                    || "x_i",
                    self.config.point.0,
                    0,
                    || Value::known(*pt.x()),
                )?;
                let y = region.assign_advice(
                    || "y_i",
                    self.config.point.1,
                    0,
                    || Value::known(*pt.y()),
                )?;
                let tr = trace_simple(*point, &self.config.clg);
                let trace = region.assign_advice(
                    || "trace",
                    self.config.trace,
                    0,
                    || prev_tr.value().copied() + Value::known(tr),
                )?;
                prev_tr.copy_advice(|| "copied value", &mut region, self.config.prev_tr_copy, 0)?;
                Ok(AssignedPair {
                    point: AssignedPoint(x, y),
                    trace,
                })
            },
        )
    }

    // fn assign_divisor(
    //     &self,
    //     mut layouter: impl Layouter<C::Base>,
    //     points: Vec<C>,
    // ) -> Result<(), Error> {
    //     layouter.assign_region(|| "divisor witness", |mut region| {
    //         let f = FunctionField::interpolate_mumford(&points);
    //         for offset in 0..points.len() {
    //             self.config.selc_ec.enable(&mut region, offset)?;
    //             region.assign_advice(|| "a_i", self.config, offset, || Value::known(f.a.coeff[offset]))?;
    //             region.assign_advice(|| "b_i", self.config, offset, || Value::known(f.b.coeff[offset]))?;
    //         }
    //         Ok(())
    //     })
    // }
}

fn random_point<C: CurveAffine>() -> C {
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
    C::from_xy(x, out).unwrap()
}

#[derive(Debug, Default)]
struct MSMCircuit<C: CurveAffine> {
    points: Vec<C>,
}

impl<C: CurveAffine> Circuit<C::Base> for MSMCircuit<C> {
    type Config = MSMConfig<C>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<C::Base>) -> Self::Config {
        MSMConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::Base>,
    ) -> Result<(), Error> {
        let chip = MSMChip::new(config);
        let mut assigned = chip.assign_first_row(layouter.namespace(|| "first row"))?;
        for i in 0..self.points.len() {
            assigned = chip.assign_point(
                layouter.namespace(|| "assign point"),
                &assigned.trace,
                &self.points[i],
            )?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::utils::function_field::random_points;
    use halo2_proofs::{dev::MockProver, halo2curves::secp256k1::Secp256k1Affine};

    use super::*;
    #[test]
    fn test_circuit() {
        let k = 4;
        let rng = &mut thread_rng();
        let points = random_points(rng, 6);
        let circuit = MSMCircuit::<Secp256k1Affine> { points };
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();

        prover.assert_satisfied();
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_circuit() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("fib-1-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Fib 1 Layout", ("sans-serif", 60)).unwrap();

        let rng = &mut thread_rng();
        let points = random_points(rng, 6);
        let circuit = MSMCircuit::<Secp256k1Affine> { points };
        halo2_proofs::dev::CircuitLayout::default()
            .render(4, &circuit, &root)
            .unwrap();
    }
}
