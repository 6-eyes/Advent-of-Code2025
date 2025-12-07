fn main() -> Result<(), Box<dyn std::error::Error>> {
    // day 1
    let res_day1_part1_example = Day1::part1("input/day1-part1-example.txt");
    println!("Day 1, part 1, example: {res_day1_part1_example}");
    let res_day1_part1 = Day1::part1("input/day1-part1.txt");
    println!("Day 1, part 1: {res_day1_part1}");

    let res_day1_part2_example = Day1::part2("input/day1-part1-example.txt");
    println!("Day 1, part 1, example: {res_day1_part2_example}");
    let res_day1_part2 = Day1::part2("input/day1-part1.txt");
    println!("Day 1, part 1: {res_day1_part2}");

    // day 2
    let res_day2_part1_example = Day2::part1("input/day2-part1-example.txt");
    println!("Day 2, part 1, example: {res_day2_part1_example}");
    let res_day2_part1 = Day2::part1("input/day2-part1.txt");
    println!("Day 2, part 1: {res_day2_part1}");

    let res_day2_part2_example = Day2::part2("input/day2-part1-example.txt");
    println!("Day 2, part 2, example: {res_day2_part2_example}");
    let res_day2_part2 = Day2::part2("input/day2-part1.txt");
    println!("Day 2, part 2: {res_day2_part2}");

    // day 3
    let res_day3_part1_example = Day3::part1("input/day3-part1-example.txt");
    println!("Day 3, part 1, example: {res_day3_part1_example}");
    let res_day3_part1 = Day3::part1("input/day3-part1.txt");
    println!("Day 3, part 1: {res_day3_part1}");

    let res_day3_part2_example = Day3::part2("input/day3-part1-example.txt");
    println!("Day 3, part 2, example: {res_day3_part2_example}");
    let res_day3_part2 = Day3::part2("input/day3-part1.txt");
    println!("Day 3, part 2: {res_day3_part2}");

    // day 4
    let res_day4_part1_example = Day4::part1("input/day4-part1-example.txt");
    println!("Day 4, part 1, example: {res_day4_part1_example}");
    let res_day4_part1 = Day4::part1("input/day4-part1.txt");
    println!("Day 4, part 1: {res_day4_part1}");

    let res_day4_part2_example = Day4::part2("input/day4-part1-example.txt");
    println!("Day 4, part 2, example: {res_day4_part2_example}");
    let res_day4_part2 = Day4::part2("input/day4-part1.txt");
    println!("Day 4, part 2: {res_day4_part2}");

    // day 5
    let res_day5_part1_example = Day5::part1("input/day5-part1-example.txt");
    println!("Day 5, part 1, example: {res_day5_part1_example}");
    let res_day5_part1 = Day5::part1("input/day5-part1.txt");
    println!("Day 5, part 1: {res_day5_part1}");

    let res_day5_part2_example = Day5::part2("input/day5-part1-example.txt");
    println!("Day 5, part 2, example: {res_day5_part2_example}");
    let res_day5_part2 = Day5::part2("input/day5-part1.txt");
    println!("Day 5, part 2: {res_day5_part2}");

    Ok(())
}

trait Day {
    fn part1(path: impl AsRef<std::path::Path>) -> u64;
    fn part2(path: impl AsRef<std::path::Path>) -> u64;
}

struct Day1;

impl Day for Day1 {
    fn part1(path: impl AsRef<std::path::Path>) -> u64 {
        let input = std::fs::read_to_string(path.as_ref()).expect("unable to read file contents");
        input.lines().fold((50, 0), |(mut pointer, mut count), l| {
            let (dir, num) = l.split_at(1);
            let num = num.parse::<u64>().expect("unable to parse number") % 100;
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

    fn part2(path: impl AsRef<std::path::Path>) -> u64 {
        let input = std::fs::read_to_string(path.as_ref()).expect("unable to read file contents");
        input.lines().fold((50, 0), |(mut pointer, mut count), l| {
            let (dir, num) = l.split_at(1);
            let mut num = num.parse::<u64>().expect("unable to parse number");
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

struct Day2;

impl Day for Day2 {
    fn part1(path: impl AsRef<std::path::Path>) -> u64 {
        let input = std::fs::read_to_string(path.as_ref()).expect("unable to read file contents");
        // even number of digits
        // 1000-9999
        // 10-99 = 89 numbers
        // 
        // 433984
        // 434 * 1000 + 434
        // (lower + 1) * 10^half + (lower + 1)
        //
        // 984433
        // 434 * 1000 + 434
        // (lower + 1) * 10^half + (lower + 1)
        //
        // L: 7180 -> 7272
        // L: 8071 -> 8080
        // U: 7180 -> 7171
        // U: 8071 -> 7979
        // 
        // 7779-9594 -> 7878-9494
        // 94 - 78 + 1 = 17
        //
        // odd digits
        // 998-1012
        // 1010-1012 L < U
        // 1010-1010
        // 1010 - 1010 + 1 = 1
        // 
        // 20-990
        // 20-99
        // 22-99
        // 9 - 2 + 1 = 8
        //
        // 20-3092
        // 20-99 and 1000-3092
        // 22-99 and 1010-3030
        // (9 - 2 + 1) + (30 - 10 + 1)

        let identify_palindrome = |l: &str, u: &str| -> u64 {
            let half = l.len() / 2;
            let start = {
                let (left, right) = l.split_at(half);
                let (left, right) = (left.parse::<u64>().unwrap(), right.parse::<u64>().unwrap());

                if left < right { left + 1 } else { left }
            };

            let end = {
                let (left, right) = u.split_at(half);
                let (left, right) = (left.parse::<u64>().unwrap(), right.parse::<u64>().unwrap());

                if left > right { left - 1 } else { left }
            };
            
            // 433433-691691
            // sum( i * 10^half + i ) for i in 433-691
            // (10^half + 1) sum(i) for i in 433-691
            // [a, b]
            // [0, b - a] + a * (b - a + 1)
            // (b - a)(b - a + 1) / 2 + ab - a^2 + a
            // ((b - a)^2 + (b - a) + 2ab - 2a^2 + 2a) / 2
            // (b^2 + a^2 - 2ab + b - a + 2ab - 2a^2 + 2a) / 2
            // (b^2 + a^2 + b + a - 2a^2) / 2
            // (b^2 - a^2 + b + a) / 2
            // ((b + a)(b - a) + (b + a)) / 2
            // (b - a)((b + a) + 1) / 2
            // (b + a)(b - a + 1) / 2

            if start > end {
                0
            }
            else {
                (10u64.pow(half as u32) + 1) * (end + start) * (end - start + 1) / 2
            }
        };

        input.split(',').fold(0, |mut acc, range| {
            let (mut l, mut u) = range.split_once('-').expect("invalid input. unable to identify range");
            assert!(l.parse::<u64>().expect("error while parsing lower bound") <= u.parse().expect("error while parsing upper bound"), "lower bound greater than upper bound");
            l = l.trim_start_matches('0');
            u = u.trim_start_matches('0');

            if l.len() != u.len() {
                // 3-8
                // 4,6,8
                // 1-5
                // 2,4
                // 4-4
                // 4
                // if lower is even
                if l.len() & 1 == 0 {
                    acc += identify_palindrome(l, "9".repeat(l.len()).as_str());
                }

                acc += (l.len() + 1..u.len()).filter(|n| n & 1 == 0).map(|n|
                    // 100100-999999
                    // 2 -> 9
                    // 4 -> 90
                    // 6 -> 900
                    // 8 -> 9000
                    9 * 10u64.pow(n as u32 / 2 - 1)
                ).sum::<u64>();

                // if upper is even
                if u.len() & 1 == 0 {
                    let half = u.len() / 2;
                    let mut start = String::with_capacity(half);
                    start.push('1');
                    start.extend(std::iter::repeat_n('0', half - 1));

                    acc += identify_palindrome(start.repeat(2).as_str(), u);
                }
            }
            else if l.len() & 1 == 0 {
                acc += identify_palindrome(l, u);
            }

            acc
        })
    }

    fn part2(path: impl AsRef<std::path::Path>) -> u64 {
        let input = std::fs::read_to_string(path).expect("unable to read file contents");
        input.split(',').fold(0, |acc, range| {
            let (l, u) = range.split_once('-').expect("unable to read range");
            let (l, u) = (l.parse::<u64>().expect("error while parsing lower bound"), u.parse().expect("error while parsing upper bound"));
            assert!(l <= u, "lower bound greater than upper bound");

            (l..=u).filter(|n| {
                let digits = n.ilog10() + 1;
                let half_digits = digits / 2;
                (1..=half_digits).filter(|i| digits % i == 0).any(|i| {
                    let den = 10u64.pow(i);
                    let repeater = n % den;
                    let mut num = n / den;

                    while num > 0 {
                        let digits_in_question = num % den;
                        if digits_in_question != repeater {
                            return false;
                        }
                        num /= den;
                    }

                    true
                })
            }).sum::<u64>() + acc
        })
    }
}

struct Day3;

impl Day for Day3 {
    fn part1(path: impl AsRef<std::path::Path>) -> u64 {
        let input = std::fs::read_to_string(path).expect("unable to read file contents");

        input.lines().map(|l| {
            let nums = l.chars().map(|c| c as u64 - '0' as u64).collect::<Vec<u64>>();
            let (tens_index, tens) = nums[..nums.len() - 1].iter().enumerate().reduce(|acc, a| if a.1 > acc.1 { a } else { acc }).expect("empty iterator");
            let ones = nums[tens_index + 1..].iter().max().expect("empty iterator");
            tens * 10  + ones
        }).sum()
    }

    fn part2(path: impl AsRef<std::path::Path>) -> u64 {
        let input = std::fs::read_to_string(path).expect("unable to read file contents");

        input.lines().map(|l| {
            let nums = l.chars().map(|c| c as u64 - '0' as u64).collect::<Vec<u64>>();
            assert!(nums.len() >= 12, "not enough batteries");
            (0..12).fold((0, 0), |(acc, min_idx), i| {
                let (nxt_idx, jolt) = nums[min_idx..nums.len() - 11 + i].iter().enumerate().reduce(|acc, a| if a.1 > acc.1 { a } else { acc }).expect("empty iterator");
                (acc + jolt * 10u64.pow((11 - i) as u32), min_idx + nxt_idx + 1)
            }).0
        }).sum()
    }
}

struct Day4;

impl Day for Day4 {
    fn part1(path: impl AsRef<std::path::Path>) -> u64 {
        let input = std::fs::read_to_string(path).expect("unable to read file contents");
        let floor = input.lines().map(|l| l.chars().map(|c| match c {
            '.' => false,
            '@' => true,
            _ => panic!("invalid character in map"),
        }).collect::<Vec<bool>>()).collect::<Vec<Vec<bool>>>();

        let rows = floor.len();
        let cols = floor.first().expect("empty map").len();
        
        (0..rows).fold(0, |acc, r|
            (0..cols).filter(|&c| floor[r][c]).fold(0, |acc, c|
                if [0, 1, 2].into_iter().flat_map(|i| [0, 1, 2].into_iter().map(move |j| (i, j))).filter(|&(i, j)|
                    !(i == 1 && j == 1) && r + i >= 1 && r + i < rows + 1 && c + j >= 1 && c + j < cols + 1 && floor[r + i - 1][c + j - 1]
                ).count() < 4 {
                    acc + 1
                }
                else {
                    acc
                }
            ) + acc
        )
    }

    fn part2(path: impl AsRef<std::path::Path>) -> u64 {
        let input = std::fs::read_to_string(path).expect("unable to read file contents");
        let floor = input.lines().map(|l| l.chars().map(|c| match c {
            '.' => false,
            '@' => true,
            _ => panic!("invalid character in map"),
        }).collect::<Vec<bool>>()).collect::<Vec<Vec<bool>>>();

        let rows = floor.len();
        let cols = floor.first().expect("empty map").len();
        
        let mut set = std::collections::HashSet::new();

        loop {
            // break if no rolls can be removed
            let pre = set.len();
            (0..rows).for_each(|r|
                (0..cols).filter(|&c| floor[r][c]).for_each(|c|
                    if [0, 1, 2].into_iter().flat_map(|i| [0, 1, 2].into_iter().map(move |j| (i, j))).filter(|&(i, j)|
                        !(i == 1 && j == 1) && r + i >= 1 && r + i < rows + 1 && c + j >= 1 && c + j < cols + 1 && !set.contains(&(r + i - 1, c + j - 1)) && floor[r + i - 1][c + j - 1]
                    ).count() < 4 {
                        set.insert((r, c));
                    }
                )
            );

            if pre == set.len() {
                break pre as u64;
            }
        }
    }
}

struct Day5;

impl Day for Day5 {
    fn part1(path: impl AsRef<std::path::Path>) -> u64 {
        let input = std::fs::read_to_string(path).expect("unable to recieve output");
        let (ranges_str, ingridients_str) = input.split_once("\n\n").expect("unabke to split input");
        let range = ranges_str.lines().fold(Vec::new(), |mut acc, range| {
            let (start, end) = range.split_once('-').expect("invalid input");
            let (start, end) = (start.parse::<u64>().expect("invalid start"), end.parse::<u64>().expect("invalid end"));
            assert!(start <= end, "start should be less then end of range");

            match acc.binary_search_by(|&(s, e)| {
                if end < s {
                    std::cmp::Ordering::Less
                }
                else if start > e {
                    std::cmp::Ordering::Greater
                }
                else {
                    std::cmp::Ordering::Equal
                }
            }) {
                Ok(i) => {
                    let ele = acc.get_mut(i).unwrap();
                    *ele = (ele.0.min(start), ele.1.max(end));
                },
                Err(i) => {
                    acc.insert(i, (start, end));
                },
            }

            acc
        });

        ingridients_str.lines().filter(|l| {
            let num = l.parse::<u64>().expect("unable to parse input");
            range.iter().any(|&(start, end)| num >= start && num <= end)
        }).count() as u64
    }

    fn part2(path: impl AsRef<std::path::Path>) -> u64 {
        let input  = std::fs::read_to_string(path).expect("unable to recieve ouput");
        let (ranges_str, _) = input.split_once("\n\n").expect("unable to split input");
        let mut ranges = ranges_str.lines().map(|range| {
            let (start, end) = range.split_once('-').expect("invalid input");
            let (start, end) = (start.parse::<u64>().expect("invalid start"), end.parse::<u64>().expect("invalid end"));
            assert!(start <= end, "start should be less then end of range");
            (start, end)
        }).collect::<Vec<(u64, u64)>>();

        ranges.sort_by_key(|e| e.0);

        let mut last_seen = None;
        let count = ranges.iter().fold(0, |mut acc, (s, e)| {
            match last_seen {
                None => last_seen = Some((s, e)),
                Some((ls, le)) if s > le => {
                    acc += le - ls + 1;
                    last_seen = Some((s, e));
                },
                Some((ls, le)) => {
                    acc += s - ls;
                    last_seen = Some((s, e.max(le)));
                }
            }

            acc
        });

        let last_seen = last_seen.unwrap();
        count + last_seen.1 - last_seen.0 + 1
    }
}