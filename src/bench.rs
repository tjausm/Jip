use std::{ops::Range, time::Instant};

use crate::see::{print_verification, Depth, ExitCode};

pub fn bench(program: &str, start: Depth, end: Depth, step: i32) -> (ExitCode, String) {
    let depths = (start..end).step_by(step.try_into().unwrap());

    println!("d        time");

    for d in depths {
        let now = Instant::now();

        // Code block to measure.
        {
            match print_verification(program, d) {
                (ExitCode::Error, e) => return (ExitCode::Error, e),
                _ => (),
            }
        }
        println!("{}       {:?}", d, now.elapsed());
    }
    return (ExitCode::Valid, "Benchmark done!".to_owned());
}
