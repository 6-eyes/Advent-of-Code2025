fn main() -> Result<(), Box<dyn std::error::Error>> {
    let res_part_1_example = Day1::part1("input/day1-part1-example.txt");
    println!("Day 1, part 1, example: {res_part_1_example}");
    let res_part_1 = Day1::part1("input/day1-part1.txt");
    println!("Day 1, part 1: {res_part_1}");

    let res_part_2_example = Day1::part2("input/day1-part1-example.txt");
    println!("Day 1, part 1, example: {res_part_2_example}");
    let res_part_2 = Day1::part2("input/day1-part1.txt");
    println!("Day 1, part 1: {res_part_2}");

    Ok(())
}

trait Day {
    fn part1(path: impl AsRef<std::path::Path>) -> u32;
    fn part2(path: impl AsRef<std::path::Path>) -> u32;
}

struct Day1;

impl Day for Day1 {
    fn part1(path: impl AsRef<std::path::Path>) -> u32 {
        let input = std::fs::read_to_string(path.as_ref()).expect("unable to read file contents");
        input.lines().fold((50, 0), |(mut pointer, mut count), l| {
            let (dir, num) = l.split_at(1);
            let num = num.parse::<u32>().expect("unable to parse number") % 100;
            match dir {
                "L" => {
                    pointer = if num > pointer {
                        100 - num + pointer
                    }
                    else {
                        pointer - num
                    };
                },
                "R" => {
                    let sum = pointer + num;
                    pointer = if sum < 100 {
                        sum
                    }
                    else {
                        sum - 100
                    };
                },
                _ => panic!("invalid input"),
            }

            if pointer == 0 {
                count += 1;
            }

            (pointer, count)
        }).1
    }

    fn part2(path: impl AsRef<std::path::Path>) -> u32 {
        let input = std::fs::read_to_string(path.as_ref()).expect("unable to read file contents");
        input.lines().fold((50, 0), |(mut pointer, mut count), l| {
            let (dir, num) = l.split_at(1);
            let mut num = num.parse::<u32>().expect("unable to parse number");
            count += num / 100;
            num %= 100;

            match dir {
                "L" => {
                    pointer = if pointer == 0 {
                        100 - num
                    }
                    else if num > pointer {
                        count += 1;
                        100 - num + pointer
                    }
                    else {
                        pointer - num
                    };
                },
                "R" => {
                    let sum = pointer + num;
                    pointer = if sum == 100 {
                        0
                    }
                    else if sum < 100 {
                        sum
                    }
                    else {
                        count  += 1;
                        sum - 100
                    };
                },
                _ => panic!("invalid input"),
            }

            if pointer == 0 {
                count += 1;
            }

            (pointer, count)
        }).1

    }
}