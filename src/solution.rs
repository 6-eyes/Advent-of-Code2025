use super::Solution;

pub(crate) struct Day1;

impl Solution for Day1 {
    fn part_1(&self, input: String) -> Box<dyn std::fmt::Display> {
        let ans = input.lines().fold((50, 0), |(mut pointer, mut count), l| {
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
        }).1;

        Box::new(ans)
    }

    fn part_2(&self, input: String) -> Box<dyn std::fmt::Display> {
        let ans = input.lines().fold((50, 0), |(mut pointer, mut count), l| {
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
        }).1;

        Box::new(ans)
    }
}

pub(crate) struct Day2;

impl Solution for Day2 {
    fn part_1(&self, input: String) -> Box<dyn std::fmt::Display> {
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

        let ans = input.split(',').fold(0, |mut acc, range| {
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
        });

        Box::new(ans)
    }

    fn part_2(&self, input: String) -> Box<dyn std::fmt::Display> {
        let ans = input.split(',').fold(0, |acc, range| {
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
        });
        
        Box::new(ans)
    }
}

pub(crate) struct Day3;

impl Solution for Day3 {
    fn part_1(&self, input: String) -> Box<dyn std::fmt::Display> {
        let ans = input.lines().map(|l| {
            let nums = l.chars().map(|c| c as u64 - '0' as u64).collect::<Vec<u64>>();
            let (tens_index, tens) = nums[..nums.len() - 1].iter().enumerate().reduce(|acc, a| if a.1 > acc.1 { a } else { acc }).expect("empty iterator");
            let ones = nums[tens_index + 1..].iter().max().expect("empty iterator");
            tens * 10  + ones
        }).sum::<u64>();

        Box::new(ans)
    }

    fn part_2(&self, input: String) -> Box<dyn std::fmt::Display> {
        let ans = input.lines().map(|l| {
            let nums = l.chars().map(|c| c as u64 - '0' as u64).collect::<Vec<u64>>();
            assert!(nums.len() >= 12, "not enough batteries");
            (0..12).fold((0, 0), |(acc, min_idx), i| {
                let (nxt_idx, jolt) = nums[min_idx..nums.len() - 11 + i].iter().enumerate().reduce(|acc, a| if a.1 > acc.1 { a } else { acc }).expect("empty iterator");
                (acc + jolt * 10u64.pow((11 - i) as u32), min_idx + nxt_idx + 1)
            }).0
        }).sum::<u64>();

        Box::new(ans)
    }
}

pub(crate) struct Day4;

impl Solution for Day4 {
    fn part_1(&self, input: String) -> Box<dyn std::fmt::Display> {
        let floor = input.lines().map(|l| l.chars().map(|c| match c {
            '.' => false,
            '@' => true,
            _ => panic!("invalid character in map"),
        }).collect::<Vec<bool>>()).collect::<Vec<Vec<bool>>>();

        let rows = floor.len();
        let cols = floor.first().expect("empty map").len();
        
        let ans = (0..rows).fold(0, |acc, r|
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
        );
        
        Box::new(ans)
    }

    fn part_2(&self, input: String) -> Box<dyn std::fmt::Display> {
        let floor = input.lines().map(|l| l.chars().map(|c| match c {
            '.' => false,
            '@' => true,
            _ => panic!("invalid character in map"),
        }).collect::<Vec<bool>>()).collect::<Vec<Vec<bool>>>();

        let rows = floor.len();
        let cols = floor.first().expect("empty map").len();
        
        let mut set = std::collections::HashSet::new();

        let ans = loop {
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
        };

        Box::new(ans)
    }
}

pub(crate) struct Day5;

impl Solution for Day5 {
    fn part_1(&self, input: String) -> Box<dyn std::fmt::Display> {
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

        let ans = ingridients_str.lines().filter(|l| {
            let num = l.parse::<u64>().expect("unable to parse input");
            range.iter().any(|&(start, end)| num >= start && num <= end)
        }).count() as u64;

        Box::new(ans)
    }

    fn part_2(&self, input: String) -> Box<dyn std::fmt::Display> {
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
        let ans = count + last_seen.1 - last_seen.0 + 1;

        Box::new(ans)
    }
}

pub(crate) struct Day6;

impl Solution for Day6 {
    fn part_1(&self, input: String) -> Box<dyn std::fmt::Display> {
        let input_lines = input.lines().collect::<Vec<&str>>();
        let numbers = input_lines[..input_lines.len() - 1].iter().map(|l| l.split_whitespace().map(|n| n.parse::<u64>().expect("unable to read input")).collect::<Vec<u64>>()).collect::<Vec<Vec<u64>>>();
        assert!(!numbers.is_empty(), "no numbers found in homework");
        
        let ans = input_lines.last().expect("undesirable input").split_whitespace().map(|s| match s.chars().next().expect("no operator found") {
            '+' => |acc, num| acc + num,
            '*' => |acc, num| acc * num,
            c => panic!("invalid operator {c}"),
        }).enumerate().map(|(i, o)| numbers.iter().map(|r| r[i]).reduce(o).expect("unable to reduce array")).sum::<u64>();

        Box::new(ans)
    }

    fn part_2(&self, input: String) -> Box<dyn std::fmt::Display> {
        let input_lines = input.lines().collect::<Vec<&str>>();

        let numbers = input_lines[..input_lines.len() - 1].iter().map(|l| l.chars().collect::<Vec<char>>()).collect::<Vec<Vec<char>>>();
        assert!(!numbers.is_empty(), "no numbers found");
        let len = numbers[0].len();

        let get_num_at_idx = |i| {
            let num = numbers.iter().map(|l| l.get(i).expect("invalid index")).collect::<String>();
            num.trim().parse::<u64>().ok()
        };


        let ans = input_lines.last().expect("undesirable input").char_indices().filter(|&(_, c)| c == '*' || c == '+').map(|(mut i, c)| {
            let mut nums = Vec::new();
            while i < len && let Some(num) = get_num_at_idx(i) {
                nums.push(num);
                i += 1;
            }

            match c {
                '+' => nums.into_iter().reduce(|acc, e| acc + e),
                '*' => nums.into_iter().reduce(|acc, e| acc * e),
                c => panic!("invalid operator {c}"),
            }.expect("unable to reduce array")
        }).sum::<u64>();

        Box::new(ans)
    }
}

pub(crate) struct Day7;

impl Solution for Day7 {
    fn part_1(&self, input: String) -> Box<dyn std::fmt::Display> {
        let mut start = None;
        let grid = input.lines().enumerate().map(|(r, l)| l.chars().enumerate().map(|(c, s)| {
            if s == 'S' {
                start = Some((r, c));
            }
            s
        }).collect::<Vec<char>>()).collect::<Vec<Vec<char>>>();

        assert!(!grid.is_empty() && !grid[0].is_empty(), "no grid found");
        assert!(start.is_some(), "source position not found");

        let mut source = std::collections::VecDeque::new();
        source.push_back(start.unwrap());

        let mut visited = std::collections::HashSet::new();
        visited.insert(start.unwrap());

        let mut count = 0;


        while let Some((r, c)) = source.pop_front() {
            let mut add = |r, c| {
                if !visited.contains(&(r, c)) {
                    visited.insert((r, c));
                    source.push_back((r, c));
                }
            };

            if grid[r][c] == '^' {
                count += 1;
                add(r, c - 1);
                add(r, c + 1);
            }
            else if r + 1 < grid.len() {
                    add(r + 1, c);
            }
        }

        Box::new(count)
    }

    fn part_2(&self, input: String) -> Box<dyn std::fmt::Display> {
        let mut start = None;
        let grid = input.lines().enumerate().map(|(r, l)| l.chars().enumerate().map(|(c, s)| {
            if s == 'S' {
                start = Some((r, c));
            }
            s
        }).collect::<Vec<char>>()).collect::<Vec<Vec<char>>>();

        assert!(!grid.is_empty() && !grid[0].is_empty(), "no grid found");
        assert!(start.is_some(), "source position not found");
        let (r, c) = start.unwrap();
        
        let mut cache = std::collections::HashMap::new();
        Box::new(Self::get_paths(&grid, r, c, &mut cache))
    }
}

impl Day7 {
    fn get_paths(grid: &[Vec<char>], r: usize, c: usize, cache: &mut std::collections::HashMap<(usize, usize), u64>) -> u64 {
        if r < grid.len() {
            if let Some(v) = cache.get(&(r, c)) {
                *v
            }
            else {
                let res = if grid[r][c] == '^' {
                    Self::get_paths(grid, r, c - 1, cache) + Self::get_paths(grid, r, c + 1, cache)
                }
                else {
                    Self::get_paths(grid, r + 1, c, cache)
                };

                cache.insert((r, c), res);
                res
            }
        }
        else {
            1
        }
    }
}

pub(crate) struct Day8;

impl Solution for Day8 {
    fn part_1(&self, input: String) -> Box<dyn std::fmt::Display> {
        // make pairs of junction boxes
        // store junction boxes position and their distance in a min heap. Min by the distance between them.
        // pop from heap until empty
        // connect and store junction boxes in a vec of set.
        // if none of the junction boxes are in the vec of set, add a new circuit in the vec.
        // if one of the junction boxes are in the vec of set, add the other one to the same set.
        // if both are in different set, join the sets.
        // if both are in same set, ignore
        // output the lengths multiplied of the 3 longest sets

        const MAX_CONNECTIONS: usize = 1000; // 10 for example

        let junction_boxes = input.lines().map(|l| {
            let mut parts = l.split(',');
            let mut next = || parts.next().expect("invalid number of coordinates");

            let parse = |i: &str| i.parse::<u64>().expect("unable to read coordinate");

            (parse(next()), parse(next()), parse(next()))
        }).collect::<Vec<(u64, u64, u64)>>();

        let distance = |first: usize, second: usize| junction_boxes[first].0.abs_diff(junction_boxes[second].0).pow(2) + junction_boxes[first].1.abs_diff(junction_boxes[second].1).pow(2) + junction_boxes[first].2.abs_diff(junction_boxes[second].2).pow(2);
        let mut pairs = (0..junction_boxes.len()).flat_map(|first| (first + 1..junction_boxes.len()).map(move |second| (std::cmp::Reverse(distance(first, second)), first, second))).collect::<std::collections::BinaryHeap<(std::cmp::Reverse<u64>, usize, usize)>>();

        let mut circuits = (0..junction_boxes.len()).collect::<Vec<usize>>();
        let mut connections = 0;

        while connections < MAX_CONNECTIONS && let Some((_, a, b)) = pairs.pop() {
            Self::merge(&mut circuits, a, b);
            connections += 1;
        }

        let mut circuit_lengths = vec!{ 0; junction_boxes.len() };
        (0..junction_boxes.len()).for_each(|i| circuit_lengths[Self::root(&mut circuits, i)] += 1);
        circuit_lengths.sort_by(|a, b| b.cmp(a));

        Box::new(circuit_lengths[0] * circuit_lengths[1] * circuit_lengths[2])
    }

    fn part_2(&self, input: String) -> Box<dyn std::fmt::Display> {
        let junction_boxes = input.lines().map(|l| {
            let mut parts = l.split(',');
            let mut next = || parts.next().expect("invalid number of coordinates");

            let parse = |i: &str| i.parse::<u64>().expect("unable to read coordinate");

            (parse(next()), parse(next()), parse(next()))
        }).collect::<Vec<(u64, u64, u64)>>();

        let distance = |first: usize, second: usize| junction_boxes[first].0.abs_diff(junction_boxes[second].0).pow(2) + junction_boxes[first].1.abs_diff(junction_boxes[second].1).pow(2) + junction_boxes[first].2.abs_diff(junction_boxes[second].2).pow(2);
        let mut pairs = (0..junction_boxes.len()).flat_map(|first| (first + 1..junction_boxes.len()).map(move |second| (std::cmp::Reverse(distance(first, second)), first, second))).collect::<std::collections::BinaryHeap<(std::cmp::Reverse<u64>, usize, usize)>>();

        let mut circuits = (0..junction_boxes.len()).collect::<Vec<usize>>();

        let mut total_circuits = junction_boxes.len();
        while let Some((_, a, b)) = pairs.pop() {
            if Self::root(&mut circuits, a) == Self::root(&mut circuits, b) {
                continue;
            }

            Self::merge(&mut circuits, a, b);
            total_circuits -= 1;

            if total_circuits == 1 {
                return Box::new(junction_boxes[a].0 * junction_boxes[b].0);
            }
        }

        panic!("unable to find optimal solution");
    }
}

impl Day8 {
    fn root(circuit: &mut [usize], ele: usize) -> usize {
        if ele == circuit[ele] {
            ele
        }
        else {
            circuit[ele] = Self::root(circuit, circuit[ele]);
            circuit[ele]
        }
    }

    fn merge(circuit: &mut [usize], a: usize, b: usize) {
        circuit[Self::root(circuit, b)] = Self::root(circuit, a);
    }
}

pub(crate) struct Day9;

impl Solution for Day9 {
    fn part_1(&self, input: String) -> Box<dyn std::fmt::Display> {
        let red_tiles = input.lines().map(|l| {
            let (x, y) = l.split_once(',').expect("unable to read input");
            let parse = |r: &str| r.parse::<u64>().expect("unable to parse coordinate number");
            (parse(x), parse(y))
        }).collect::<Vec<(u64, u64)>>();

        let (c1, c2) = (0..red_tiles.len()).flat_map(|c1| (c1 + 1..red_tiles.len()).map(move |c2| (c1, c2))).max_by(|&c1, &c2| {
            let area = |(c1_idx, c2_idx): (usize, usize)| red_tiles[c1_idx].0.abs_diff(red_tiles[c2_idx].0) + red_tiles[c1_idx].1.abs_diff(red_tiles[c2_idx].1);
            area(c1).cmp(&area(c2))
        }).expect("no adjacent red tiles found");
    
        Box::new((red_tiles[c1].0.abs_diff(red_tiles[c2].0) + 1) * (red_tiles[c1].1.abs_diff(red_tiles[c2].1) + 1))
    }

    fn part_2(&self, input: String) -> Box<dyn std::fmt::Display> {
        let red_tiles = input.lines().map(|l| {
            let (x, y) = l.split_once(',').expect("unable to read input");
            let parse = |r: &str| r.parse::<u64>().expect("unable to parse coordinate number");
            (parse(x), parse(y))
        }).collect::<Vec<(u64, u64)>>();

        // add the first tile to incorporate the last pair of tiles
        // red_tiles.push(red_tiles.get(0).copied().expect("empty input"));

        assert!(red_tiles.windows(2).chain(std::iter::once([red_tiles.last().copied().unwrap(), red_tiles.first().copied().unwrap()].as_slice())).all(|ele| (ele[0].0 == ele[1].0 && ele[0].1 != ele[1].1) || (ele[0].0 != ele[1].0 && ele[0].1 == ele[1].1)), "tiles doesn't form a polygon");
        // make a smaller similar map
        let (x_coords, y_coords) = {
            let (mut x_coords, mut y_coords): (Vec<u64>, Vec<u64>) = red_tiles.iter().copied().unzip();
            let sort_and_dedup = |v: &mut Vec<u64>| {
                v.sort_unstable();
                v.dedup();
            };

            sort_and_dedup(&mut x_coords);
            sort_and_dedup(&mut y_coords);

            (x_coords, y_coords)
        };

        //  --> x
        // |
        // |
        // v
        // y

        let (x_len, y_len) = (2 * x_coords.len() - 1, 2 * y_coords.len() - 1);
        let grid = { // this block builds compressed grid
            let mut grid = red_tiles.windows(2).chain(std::iter::once([red_tiles.last().copied().unwrap(), red_tiles.first().copied().unwrap()].as_slice())).fold(vec!{ vec!{false; x_len}; y_len}, |mut acc, ele| {
                // compressed map coordinates
                let mut iter = ele.iter().map(|(x, y)| (x_coords.binary_search(x).unwrap() * 2, y_coords.binary_search(y).unwrap() * 2));
                let (x1, y1) = iter.next().unwrap();
                let (x2, y2) = iter.next().unwrap();

                acc.iter_mut().take(y1.max(y2) + 1).skip(y1.min(y2)).for_each(|row| row.iter_mut().take(x1.max(x2) + 1).skip(x1.min(x2)).for_each(|e| *e = true));

                acc
            });

            // flood fill the grid. considering the points outside the grid are lesser
            let mut outer_points = std::collections::HashSet::new();
            outer_points.insert((-1, -1));
            let mut queue = std::collections::VecDeque::new();
            queue.push_back((-1, -1));
            
            while let Some((a, b)) = queue.pop_front() {
                // boundary check
                [(a + 1, b), (a - 1, b), (a, b - 1), (a, b + 1)].into_iter().for_each(|(y, x)| {
                    if x < -1 || x > x_len as i32 || y < -1 || y > y_len as i32 || // boundary points
                        (x > -1 && x < x_len as i32 && y > -1 && y < y_len as i32 && grid[y as usize][x as usize]) || // valid grid points and tile boundary
                        outer_points.contains(&(y, x)) // already an outside point
                    {
                        return;
                    }

                    outer_points.insert((y, x));
                    queue.push_back((y, x));
                });
            }

            // fill the inner points
            grid.iter_mut().enumerate().for_each(|(y, row)| row.iter_mut().enumerate().filter(|(x, _)| !outer_points.contains(&(y as i32, *x as i32))).for_each(|(_, col)| *col = true));

            grid
        };

        // visualize
        // grid.iter().for_each(|row| {
        //     row.iter().for_each(|&c| print!("{} ", if c { '#' } else { '.' }));
        //     println!()
        // });

        // https://youtu.be/toDrFDh7VNs?si=8_jtANF_JtkgPtBV&t=1546
        // we use prefix sum array to determine the areas.
        // if the area is equal to the number of the elements with true in the grid, then the rectangle is valid

        let mut psa = vec!{ vec!{ 0; x_len }; y_len };
        (0..y_len).for_each(|y| (0..x_len).for_each(|x| {
            let left = if x > 0 { psa[y][x - 1] } else { 0 };
            let top = if y > 0 { psa[y - 1][x] } else { 0 };
            let topleft = if x > 0 && y > 0 { psa[y - 1][x - 1] } else { 0 };
            let grid = if grid[y][x] { 1 } else { 0 };
            psa[y][x] = left + top - topleft + grid;
        }));

        let ans = red_tiles.iter().enumerate().flat_map(|(x, &c1)| red_tiles[x + 1..].iter().map(move |&c2| (c1, c2))).filter(|(c1, c2)| {
            let compressed_coordinate = |(x, y): &(u64, u64)| (x_coords.binary_search(x).unwrap() * 2, y_coords.binary_search(y).unwrap() * 2);
            let (mut cx1, mut cy1) = compressed_coordinate(c1);
            let (mut cx2, mut cy2) = compressed_coordinate(c2);

            (cx1, cx2) = (cx1.min(cx2), cx1.max(cx2));
            (cy1, cy2) = (cy1.min(cy2), cy1.max(cy2));


            let left = if cx1 > 0 { psa[cy2][cx1 - 1] } else { 0 };
            let top = if cy1 > 0 { psa[cy1 - 1][cx2] } else { 0 };
            let topleft = if cx1 > 0 && cy1 > 0 { psa[cy1 - 1][cx1 - 1] } else { 0 };
            psa[cy2][cx2] + topleft - left - top == (cy2 - cy1 + 1) * (cx2 - cx1 + 1)
        }).map(|(c1, c2)| (c1.0.abs_diff(c2.0) + 1) * (c1.1.abs_diff(c2.1) + 1)).max().unwrap();

        Box::new(ans)
    }
}

pub(crate) struct Day10;

impl Solution for Day10 {
    fn part_1(&self, input: String) -> Box<dyn std::fmt::Display> {
        let ans = input.lines().map(|l| {
            let elements = l.split_whitespace().collect::<Vec<&str>>();
            let target = elements[0].trim_start_matches('[').trim_end_matches(']').chars().map(|c| match c {
                '#' => true,
                '.' => false,
                c => panic!("invalid character {c} in target light sequence."),
            }).collect::<Vec<bool>>();

            let buttons = elements[1..elements.len() - 1].iter().map(|e| e.trim_start_matches('(').trim_end_matches(')').split(',').map(|num| num.parse::<usize>().inspect(|&n| assert!(target.len() > n, "button index out of bounds of target sequence")).expect("unable to parse button index sequence")).collect::<Vec<usize>>()).collect::<Vec<Vec<usize>>>();

            // bfs
            let mut queue = std::collections::VecDeque::new();
            queue.push_back((vec!{ false; target.len() }, None, 0));

            let mut seen = std::collections::HashSet::new();
            seen.insert(vec!{ false; target.len() });

            while let Some((state, last_pressed, mut count)) = queue.pop_front() {
                count += 1;

                for (i, button) in buttons.iter().enumerate().filter(|&(i, _)| last_pressed.is_none_or(|idx| idx == i)) {
                    let mut new_state = state.clone();
                    // apply
                    button.iter().for_each(|&l| new_state[l] = !new_state[l]);

                    if new_state == target {
                        return count
                    }
                    
                    if !seen.contains(&new_state) {
                        queue.push_back((new_state.clone(), Some(i), count));
                        seen.insert(new_state);
                    }
                }
            }

            0
        }).sum::<u32>();

        Box::new(ans)
    }

    fn part_2(&self, input: String) -> Box<dyn std::fmt::Display> {
        let ans = input.lines().skip(29).take(1).map(|l| {
            let elements = l.split_whitespace().skip(1).collect::<Vec<&str>>();
            let mut target = elements[elements.len() - 1].trim_start_matches('{').trim_end_matches('}').split(',').map(|n| n.parse::<i32>().expect("unable to parse joltage")).collect::<Vec<i32>>();
            let (rows, cols) = (target.len(), elements.len() - 1);
            let mut buttons = elements[..cols].iter().enumerate().fold(vec!{ vec!{ 0; cols }; rows }, |mut acc, (b, l)| {
                l.trim_start_matches('(').trim_end_matches(')').split(',').map(|n| n.parse::<usize>().expect("unable to parse button input")).for_each(|i| acc[i][b] = 1);
                acc
            });
            println!(); buttons.iter().for_each(|r| { r.iter().for_each(|c| print!("{c} ")); println!(); });
            println!("target: {target:?}");

            match rows.cmp(&cols) {
                std::cmp::Ordering::Less => {
                    // identify max for each button.
                    let mut max = (0..cols).fold(vec!{ 0; cols }, |mut acc, j| {
                        acc[j] = (0..rows).filter(|&i| buttons[i][j] == 1).map(|i| target[i]).min().unwrap();
                        acc
                    });

                    // these number of elements are iterated for bfs
                    let mut independent = cols - rows;

                    // gaussian elimination
                    // all elements in matrix should be integers
                    for c in 0..cols.min(rows) {
                        let swap = buttons[c][c] == 0 || buttons[c][c + 1..].iter().any(|e: &i32| e % buttons[c][c] != 0) || target[c] % buttons[c][c] != 0;
                        if swap {
                            match (c + 1..rows).find(|&r| buttons[r][c] != 0) {
                                // swap rows
                                Some(s) => {
                                    buttons.swap(c, s);
                                    // update target
                                    target.swap(c, s);
                                },
                                // swap cols
                                None => match (c + 1..cols).find(|&n| buttons[c][n] != 0) {
                                    Some(s) => {
                                        (0..rows).for_each(|i| (buttons[i][c], buttons[i][s]) = (buttons[i][s], buttons[i][c]));
                                        // update max
                                        (max[c], max[s]) = (max[s], max[c]);
                                    },
                                    None => {
                                        assert!(cols - c >= independent);
                                        independent = cols - c;
                                        println!("independent_cols: {independent}");
                                        break;
                                    }
                                },
                            }
                        }

                        // normalize row
                        let pivot = buttons[c][c];
                        buttons[c].iter_mut().for_each(|e| *e /= pivot);
                        target[c] /= pivot;

                        (0..rows).filter(|&i| i != c).for_each(|i| if buttons[i][c] != 0 {
                            let multiplier = buttons[i][c];
                            (c..cols).for_each(|n| buttons[i][n] -= multiplier * buttons[c][n]);
                            target[i] -= multiplier * target[c];
                        });
                    }
            println!(); buttons.iter().for_each(|r| { r.iter().for_each(|c| print!("{c} ")); println!(); });
            println!("target: {target:?}");

                    let get_dependent_state = |i: &[i32]| {
                        assert_eq!(i.len(), independent, "invalid length of independent variables");
                        (0..cols - independent).map(|r| target[r] - (0..independent).map(|n| buttons[r][cols + n - independent] * i[n]).sum::<i32>()).collect::<Vec<i32>>()
                    };

                    let mut queue = std::collections::VecDeque::new();
                    queue.push_back(vec!{0; independent});

                    let mut seen = std::collections::HashSet::new();
                    seen.insert(vec!{ 0; independent });

                    let mut min = i32::MAX;
                    while let Some(state) = queue.pop_front() {
                        for i in 0..independent {
                            let mut new_state = state.clone();
                            new_state[i] += 1;

                            if new_state.iter().enumerate().any(|(j, &e)| e > max[cols + j - independent]) || seen.contains(&new_state) {
                                continue;
                            }

                            seen.insert(new_state.clone());

                            let dependent_state = get_dependent_state(&new_state);
                            // println!("checking state: {new_state:?}");
                            // println!("dep state: {dependent_state:?}");
                            if dependent_state.iter().all(|&v| v >= 0) {
                                let sum = dependent_state.iter().sum::<i32>() + new_state.iter().sum::<i32>();
                                if sum < min {
                                    min = sum;
                                }
                            }

                            queue.push_back(new_state);
                            // dependent_vars.iter().chain(&new_state).for_each(|e| print!("{e} "));
                            // println!();
                        }
                    }

                    println!("min: {min}");

                    0
                },
                std::cmp::Ordering::Equal => {
                    0
                },
                std::cmp::Ordering::Greater => {
                    0
                },
            }
        }).sum::<i32>();

        Box::new(ans)
    }
}

pub(crate) struct Day11;

impl Solution for Day11 {
    fn part_1(&self, input: String) -> Box<dyn std::fmt::Display> {
        let map = input.lines().map(|l| {
            let (i, o) = l.split_once(':').expect("invalid input");
            (i, o.split_whitespace().collect::<std::collections::HashSet<&str>>())
        }).collect::<std::collections::HashMap<&str, std::collections::HashSet<&str>>>();

        let mut cache = std::collections::HashMap::new();
        Box::new(Self::count_paths(&map, "you", "out", &mut cache))
    }

    fn part_2(&self, input: String) -> Box<dyn std::fmt::Display> {
        let map = input.lines().map(|l| {
            let (i, o) = l.split_once(':').expect("invalid input");
            (i, o.split_whitespace().collect::<std::collections::HashSet<&str>>())
        }).collect::<std::collections::HashMap<&str, std::collections::HashSet<&str>>>();

        let mut cache = std::collections::HashMap::new();
        let ans = Self::count_paths(&map, "svr", "fft", &mut cache) * Self::count_paths(&map, "fft", "dac", &mut cache) * Self::count_paths(&map, "dac", "out", &mut cache) +
            Self::count_paths(&map, "svr", "dac", &mut cache) * Self::count_paths(&map, "dac", "fft", &mut cache) * Self::count_paths(&map, "fft", "out", &mut cache);

        Box::new(ans)
    }
}

impl Day11 {
    fn count_paths<'a>(map: &'a std::collections::HashMap<&str, std::collections::HashSet<&str>>, i: &'a str, o: &'a str, cache: &mut std::collections::HashMap<(&'a str, &'a str), u64>) -> u64 {
        if i == o {
            1
        }
        else if let Some(&v) = cache.get(&(i, o)) {
            v
        }
        else if let Some(paths) = map.get(i) {
            let s = paths.iter().map(|p| Self::count_paths(map, p, o, cache)).sum::<u64>();
            cache.insert((i, o), s);
            s
        }
        else {
            0
        }
    }
}