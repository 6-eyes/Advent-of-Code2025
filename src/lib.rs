mod solution;

pub fn init() {
    let mut args  = std::env::args();
    args.next();

    const INFO: &str = "\n\nWhich day to solve? Run 'cargo run -- ${day number} ${part number}'\nTo initialize new files for new day run `cargo run -- ${day number} init\n\n";
    let day = args.next().expect(INFO).parse::<u8>().unwrap_or_else(|_| {
        eprintln!("unable to parse day input");
        std::process::exit(1);
    });

    let arg = args.next().expect("\n\nWhich part to solve? Run 'cargo run -- ${day number} ${part number}'\nTo initialize new files for new day run `cargo run -- ${day number} init`\n\n");
    
    if arg == "init" {
        create(day).unwrap_or_else(|e| {
            eprintln!("unable to initilize day {day}. {e}");
            std::process::exit(7);
        });

        return;
    }

    let part = Part::parse(arg);

    let path = match args.next() {
        Some(arg) if arg == "test" || arg == "t" => format!("input/day{day}-part1-example.txt"),
        Some(arg) => {
            eprintln!("Invalid argument {} passed. Run 'cargo run -- 1 test' to run test code", arg);
            std::process::exit(3);
        },
        None => format!("input/day{day}-part1.txt"),
    };

    let input = std::fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("unable to read file input {e}");
        std::process::exit(4);
    });

    let sol = get_day(day);

    let instant = std::time::Instant::now();
    let ans = match part {
        Part::One => sol.part_1(input),
        Part::Two => sol.part_2(input),
    };
    let elapsed = instant.elapsed();

    println!("ans: {ans} Time taken {elapsed:?}");
}

fn create(day: u8) -> Result<(), std::io::Error> {
    let create = |file: String| -> Result<(), std::io::Error> {
        if !std::fs::exists(&file)? {
            std::fs::File::create(&file)?;
            println!("created file: {file}");
        }
        Ok(())
    };

    create(format!("input/day{day}-part1-example.txt"))?;
    create(format!("input/day{day}-part1.txt"))?;

    Ok(())
}

fn get_day(day: u8) -> Box<dyn Solution> {
    match day {
        1 => Box::new(solution::Day1),
        2 => Box::new(solution::Day2),
        3 => Box::new(solution::Day3),
        4 => Box::new(solution::Day4),
        5 => Box::new(solution::Day5),
        6 => Box::new(solution::Day6),
        7 => Box::new(solution::Day7),
        8 => Box::new(solution::Day8),
        // 9 => Box::new(solution::Day9),
        // 10 => Box::new(solution::Day10),
        // 11 => Box::new(solution::Day11),
        // 12 => Box::new(solution::Day12),
        d => {
            eprintln!("Day {d} yet to come!");
            std::process::exit(6);
        },
    }
}

trait Solution {
    fn part_1(&self, input: String) -> Box<dyn std::fmt::Display>;
    fn part_2(&self, input: String) -> Box<dyn std::fmt::Display>;
}

enum Part {
    One,
    Two,
}

impl Part {
    fn parse(input: String) -> Self {
        match input.as_str() {
            "1" | "One" | "one" | "ONE" => Self::One,
            "2" | "Two" | "two" | "TWO" => Self::Two,
             i =>  {
                eprintln!("invalid part input {i}");
                std::process::exit(5);
             },
        }
    }
}

impl std::fmt::Display for Part {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{0}", match self {
            Self::One => "1",
            Self::Two => "2",
        })
    }
}