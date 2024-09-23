// Copyright 2024 tison <wander4096@gmail.com>
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::ops::RangeInclusive;

use winnow::ascii::dec_uint;
use winnow::combinator::alt;
use winnow::combinator::eof;
use winnow::combinator::separated;
use winnow::error::ContextError;
use winnow::error::ErrMode;
use winnow::error::ErrorKind;
use winnow::error::FromExternalError;
use winnow::stream::Stream;
use winnow::token::literal;
use winnow::token::take_while;
use winnow::PResult;
use winnow::Parser;

use crate::sort_out_possible_values;
use crate::Crontab;
use crate::Error;
use crate::PossibleLiterals;
use crate::PossibleValue;

/// Normalize a crontab expression to compact form.
///
/// ```rust
/// use cronexpr::normalize_crontab;
///
/// assert_eq!(
///     normalize_crontab("  *   * * * * Asia/Shanghai  "),
///     "* * * * * Asia/Shanghai"
/// );
/// assert_eq!(
///     normalize_crontab("  2\t4 * * *\nAsia/Shanghai  "),
///     "2 4 * * * Asia/Shanghai"
/// );
/// ```
pub fn normalize_crontab(input: &str) -> String {
    input
        .split_ascii_whitespace()
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>()
        .join(" ")
}

/// Parse a crontab expression to [`Crontab`].
///
/// ```rust
/// use cronexpr::parse_crontab;
///
/// parse_crontab("* * * * * Asia/Shanghai").unwrap();
/// parse_crontab("2 4 * * * Asia/Shanghai").unwrap();
/// parse_crontab("2 4 * * 0-6 Asia/Shanghai").unwrap();
/// parse_crontab("2 4 */3 * 0-6 Asia/Shanghai").unwrap();
/// ```
pub fn parse_crontab(input: &str) -> Result<Crontab, Error> {
    let normalized = normalize_crontab(input);

    log::debug!("normalized input {input:?} to {normalized:?}");

    let minutes_start = 0;
    let minutes_end = normalized.find(' ').unwrap_or(normalized.len());
    let minutes_part = &normalized[..minutes_end];
    let minutes = parse_minutes
        .parse(minutes_part)
        .map_err(|err| format_parse_error(&normalized, minutes_start, err))?;

    let hours_start = minutes_end + 1;
    let hours_end = normalized[hours_start..]
        .find(' ')
        .map(|i| i + hours_start)
        .unwrap_or_else(|| normalized.len());
    let hours_part = &normalized[hours_start..hours_end];
    let hours = parse_hours
        .parse(hours_part)
        .map_err(|err| format_parse_error(&normalized, hours_start, err))?;

    let days_of_month_start = hours_end + 1;
    let days_of_month_end = normalized[days_of_month_start..]
        .find(' ')
        .map(|i| i + days_of_month_start)
        .unwrap_or_else(|| normalized.len());
    let days_of_month_part = &normalized[days_of_month_start..days_of_month_end];
    let days_of_month = parse_days_of_month
        .parse(days_of_month_part)
        .map_err(|err| format_parse_error(&normalized, days_of_month_start, err))?;

    let months_start = days_of_month_end + 1;
    let months_end = normalized[months_start..]
        .find(' ')
        .map(|i| i + months_start)
        .unwrap_or_else(|| normalized.len());
    let months_part = &normalized[months_start..months_end];
    let months = parse_months
        .parse(months_part)
        .map_err(|err| format_parse_error(&normalized, months_start, err))?;

    let days_of_week_start = months_end + 1;
    let days_of_week_end = normalized[days_of_week_start..]
        .find(' ')
        .map(|i| i + days_of_week_start)
        .unwrap_or_else(|| normalized.len());
    let days_of_week_part = &normalized[days_of_week_start..days_of_week_end];
    let days_of_week = parse_days_of_week
        .parse(days_of_week_part)
        .map_err(|err| format_parse_error(&normalized, days_of_week_start, err))?;

    let timezone_start = days_of_week_end + 1;
    let timezone_end = normalized.len();
    let timezone_part = &normalized[timezone_start..timezone_end];
    let timezone = parse_timezone
        .parse(timezone_part)
        .map_err(|err| format_parse_error(&normalized, timezone_start, err))?;

    Ok(Crontab {
        minutes,
        hours,
        days_of_month,
        months,
        days_of_week,
        timezone,
    })
}

fn format_parse_error(
    input: &str,
    start: usize,
    parse_error: winnow::error::ParseError<&str, ContextError>,
) -> Error {
    let context = "failed to parse crontab expression";

    let offset = start + parse_error.offset();
    let indent = " ".repeat(offset);

    let error = parse_error.into_inner().to_string();
    let error = if error.is_empty() {
        "malformed expression"
    } else {
        &error
    };

    Error(format!("{context}:\n{input}\n{indent}^ {error}"))
}

fn parse_timezone(input: &mut &str) -> PResult<jiff::tz::TimeZone> {
    take_while(0.., |_| true)
        .try_map_cut(|timezone| {
            jiff::tz::TimeZone::get(timezone).map_err(|_| {
                Error(format!(
                    "failed to find timezone {timezone}; \
                for a list of time zones, see the list of tz database time zones on Wikipedia: \
                https://en.wikipedia.org/wiki/List_of_tz_database_time_zones#List"
                ))
            })
        })
        .parse_next(input)
}

fn parse_asterisk<'a>(
    range: fn() -> RangeInclusive<u8>,
) -> impl Parser<&'a str, RangeInclusive<u8>, ContextError> {
    "*".map(move |_| range())
}

fn parse_single_number<'a>(
    range: fn() -> RangeInclusive<u8>,
) -> impl Parser<&'a str, u8, ContextError> {
    dec_uint.try_map_cut(move |n: u64| ensure_number_in_range(n, range()))
}

fn parse_single_day_of_week(input: &mut &str) -> PResult<u8> {
    alt((
        "SUN".map(|_| 0),
        "MON".map(|_| 1),
        "TUE".map(|_| 2),
        "WED".map(|_| 3),
        "THU".map(|_| 4),
        "FRI".map(|_| 5),
        "SAT".map(|_| 6),
    ))
    .parse_next(input)
}

fn parse_range<'a, P>(
    range: fn() -> RangeInclusive<u8>,
    parse_single_range_bound: P,
) -> impl Parser<&'a str, RangeInclusive<u8>, ContextError>
where
    P: Parser<&'a str, u8, ContextError> + Copy,
{
    (parse_single_range_bound, "-", parse_single_range_bound).try_map_cut(
        move |(lo, _, hi): (u64, _, u64)| ensure_number_range_in_range(lo, hi, range()),
    )
}

fn parse_step<'a, P>(
    range: fn() -> RangeInclusive<u8>,
    parse_single_range_bound: P,
) -> impl Parser<&'a str, RangeInclusive<u8>, ContextError>
where
    P: Parser<&'a str, u8, ContextError> + Copy,
{
    let possible_values = alt((
        parse_asterisk(range),
        parse_range(range, parse_single_range_bound),
        parse_single_range_bound.map(|n| n..=*range().end()),
    ));

    (possible_values, "/", dec_uint).try_map_cut(
        move |(candidates, _, step): (RangeInclusive<u8>, _, u64)| {
            let range = range();

            if step == 0 {
                return Err(Error("step must be greater than 0".to_string()));
            }

            if step > u8::MAX as u64 {
                return Err(Error(format!(
                    "step must be in range {range:?}; found {step}"
                )));
            }

            let step = step as u8;
            if !range.contains(&step) {
                return Err(Error(format!(
                    "step must be in range {range:?}; found {step}"
                )));
            }

            let mut values = Vec::new();
            for n in candidates.step_by(step as usize) {
                values.push(n);
            }
            Ok(values)
        },
    )
}

fn ensure_number_in_range(n: u64, range: RangeInclusive<u8>) -> Result<u8, Error> {
    if n > u8::MAX as u64 {
        return Err(Error(format!(
            "value must be in range {range:?}; found {n}"
        )));
    }

    let n = n as u8;
    if range.contains(&n) {
        Ok(n)
    } else {
        Err(Error(format!(
            "value must be in range {range:?}; found {n}"
        )))
    }
}

fn ensure_number_range_in_range(
    lo: u64,
    hi: u64,
    range: RangeInclusive<u8>,
) -> Result<RangeInclusive<u8>, Error> {
    if lo > hi {
        return Err(Error(format!(
            "range must be in ascending order; found {lo}-{hi}"
        )));
    }

    if lo > u8::MAX as u64 {
        return Err(Error(format!(
            "range must be in range {range:?}; found {lo}-{hi}"
        )));
    }

    if hi > u8::MAX as u64 {
        return Err(Error(format!(
            "range must be in range {range:?}; found {lo}-{hi}"
        )));
    }

    let lo = lo as u8;
    let hi = hi as u8;
    if range.contains(&lo) && range.contains(&hi) {
        Ok(lo..=hi)
    } else {
        Err(Error(format!(
            "range must be in range {range:?}; found {lo}-{hi}"
        )))
    }
}

trait ParserExt<I, O, E>: Parser<I, O, E> {
    #[inline(always)]
    fn try_map_cut<G, O2, E2>(self, map: G) -> TryMapCut<Self, G, I, O, O2, E, E2>
    where
        Self: Sized,
        G: FnMut(O) -> Result<O2, E2>,
        I: Stream,
        E: FromExternalError<I, E2>,
    {
        TryMapCut::new(self, map)
    }
}

struct TryMapCut<F, G, I, O, O2, E, E2>
where
    F: Parser<I, O, E>,
    G: FnMut(O) -> Result<O2, E2>,
    I: Stream,
    E: FromExternalError<I, E2>,
{
    parser: F,
    map: G,
    i: core::marker::PhantomData<I>,
    o: core::marker::PhantomData<O>,
    o2: core::marker::PhantomData<O2>,
    e: core::marker::PhantomData<E>,
    e2: core::marker::PhantomData<E2>,
}

impl<F, G, I, O, O2, E, E2> TryMapCut<F, G, I, O, O2, E, E2>
where
    F: Parser<I, O, E>,
    G: FnMut(O) -> Result<O2, E2>,
    I: Stream,
    E: FromExternalError<I, E2>,
{
    #[inline(always)]
    fn new(parser: F, map: G) -> Self {
        Self {
            parser,
            map,
            i: Default::default(),
            o: Default::default(),
            o2: Default::default(),
            e: Default::default(),
            e2: Default::default(),
        }
    }
}

impl<F, G, I, O, O2, E, E2> Parser<I, O2, E> for TryMapCut<F, G, I, O, O2, E, E2>
where
    F: Parser<I, O, E>,
    G: FnMut(O) -> Result<O2, E2>,
    I: Stream,
    E: FromExternalError<I, E2>,
{
    #[inline]
    fn parse_next(&mut self, input: &mut I) -> PResult<O2, E> {
        let start = input.checkpoint();
        let o = self.parser.parse_next(input)?;

        (self.map)(o).map_err(|err| {
            input.reset(&start);
            ErrMode::from_external_error(input, ErrorKind::Verify, err).cut()
        })
    }
}

impl<I, O, E, P> ParserExt<I, O, E> for P where P: Parser<I, O, E> {}

#[cfg(test)]
mod tests {
    use insta::assert_debug_snapshot;
    use insta::assert_snapshot;

    use super::*;
    use crate::setup_logging;

    #[test]
    fn test_parse_crontab() {
        setup_logging();

        // old cases - since insta name anon cases by order, let's leave it as is
        assert_debug_snapshot!(parse_crontab("* * * * * Asia/Shanghai").unwrap());
        assert_debug_snapshot!(parse_crontab("2 4 * * * Asia/Shanghai").unwrap());
        assert_debug_snapshot!(parse_crontab("2 4 * * 0-6 Asia/Shanghai").unwrap());
        assert_debug_snapshot!(parse_crontab("2 4 */3 * 0-6 Asia/Shanghai").unwrap());
        assert_debug_snapshot!(parse_crontab("*/2 1 1 1 * Asia/Shanghai").unwrap());
        assert_debug_snapshot!(parse_crontab("1/2 1 1 1 * Asia/Shanghai").unwrap());
        assert_debug_snapshot!(parse_crontab("1-29/2 1 1 1 * Asia/Shanghai").unwrap());
        assert_debug_snapshot!(parse_crontab("1-30/2 1 1 1 * Asia/Shanghai").unwrap());
        assert_debug_snapshot!(parse_crontab("1,2,10 1 1 1 * Asia/Shanghai").unwrap());
        assert_debug_snapshot!(parse_crontab("1-10,2,10,50 1 1 1 * Asia/Shanghai").unwrap());
        assert_snapshot!(parse_crontab("invalid 4 * * * Asia/Shanghai").unwrap_err());
        assert_snapshot!(parse_crontab("* * * * * Unknown/Timezone").unwrap_err());
        assert_snapshot!(parse_crontab("* 5-4 * * * Asia/Shanghai").unwrap_err());
        assert_snapshot!(parse_crontab("10086 * * * * Asia/Shanghai").unwrap_err());
        assert_snapshot!(parse_crontab("* 0-24 * * * Asia/Shanghai").unwrap_err());
        assert_snapshot!(parse_crontab("* * * 25 * Asia/Shanghai").unwrap_err());
        assert_snapshot!(parse_crontab("32-300 * * * * Asia/Shanghai").unwrap_err());
        assert_snapshot!(parse_crontab("129-300 * * * * Asia/Shanghai").unwrap_err());
        assert_snapshot!(parse_crontab("29- * * * * Asia/Shanghai").unwrap_err());
        assert_snapshot!(parse_crontab("29 ** * * * Asia/Shanghai").unwrap_err());
        assert_snapshot!(parse_crontab("29--30 * * * * Asia/Shanghai").unwrap_err());
        assert_snapshot!(parse_crontab("1,2,10,100 1 1 1 * Asia/Shanghai").unwrap_err());
        assert_snapshot!(parse_crontab("104,2,10,100 1 1 1 * Asia/Shanghai").unwrap_err());
        assert_snapshot!(parse_crontab("1,2,10 * * 104,2,10,100 * Asia/Shanghai").unwrap_err());
    }

    #[test]
    fn test_crontab_guru_examples() {
        // crontab.guru examples: https://crontab.guru/examples.html

        assert_debug_snapshot!(parse_crontab("* * * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("*/2 * * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("1-59/2 * * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("*/3 * * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("*/4 * * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("*/5 * * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("*/6 * * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("*/10 * * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("*/15 * * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("*/20 * * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("*/30 * * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("30 * * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 * * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 */2 * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 */3 * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 */4 * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 */6 * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 */8 * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 */12 * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 9-17 * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 0 * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 1 * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 2 * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 8 * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 9 * * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 0 * * 0 UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 0 * * 1 UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 0 * * 2 UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 0 * * 3 UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 0 * * 4 UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 0 * * 5 UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 0 * * 6 UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 0 * * 1-5 UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 0 * * 6,0 UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 0 1 * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 0 1 * * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 0 1 */2 * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 0 1 */3 * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 0 1 */6 * UTC").unwrap());
        assert_debug_snapshot!(parse_crontab("0 0 1 1 * UTC").unwrap());
    }
}
