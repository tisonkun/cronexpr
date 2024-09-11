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
use winnow::error::ContextError;
use winnow::token::literal;
use winnow::token::take_while;
use winnow::PResult;
use winnow::Parser;

use crate::sort_out_possible_values;
use crate::Crontab;
use crate::PossibleLiterals;
use crate::PossibleValue;

#[derive(Debug, Clone, thiserror::Error)]
#[error("{0}")]
pub struct ParseError(String);

#[derive(Debug, Clone, thiserror::Error)]
#[error("{0}")]
struct StringContext(String);

pub fn parse_crontab(input: &str) -> Result<Crontab, ParseError> {
    let normalized = input
        .split_ascii_whitespace()
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>()
        .join(" ");

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
) -> ParseError {
    let context = "failed to parse crontab expression";

    let offset = start + parse_error.offset();
    let indent = " ".repeat(offset);

    let error = parse_error.into_inner().to_string();
    let error = if error.is_empty() {
        "malformed expression"
    } else {
        &error
    };

    ParseError(format!("{context}:\n{input}\n{indent}^ {error}"))
}

fn parse_minutes(input: &mut &str) -> PResult<PossibleLiterals> {
    let values = alt((
        parse_asterisk_with_range(0..=59),
        parse_single_number_in_range(0..=59).map(|n| vec![PossibleValue::Literal(n)]),
    ))
    .parse_next(input)?;
    Ok(sort_out_possible_values(values))
}

fn parse_hours(input: &mut &str) -> PResult<PossibleLiterals> {
    let values = alt((
        parse_asterisk_with_range(0..=23),
        parse_single_number_in_range(0..=23).map(|n| vec![PossibleValue::Literal(n)]),
    ))
    .parse_next(input)?;
    Ok(sort_out_possible_values(values))
}

fn parse_months(input: &mut &str) -> PResult<PossibleLiterals> {
    let values = alt((
        parse_asterisk_with_range(1..=12),
        parse_single_number_in_range(1..=12).map(|n| vec![PossibleValue::Literal(n)]),
    ))
    .parse_next(input)?;
    Ok(sort_out_possible_values(values))
}

fn parse_days_of_week(input: &mut &str) -> PResult<PossibleLiterals> {
    let values = alt((
        parse_asterisk_with_range(1..=7),
        parse_single_number_in_range(0..=7).map(|n| vec![PossibleValue::Literal(n % 7 + 1)]),
    ))
    .parse_next(input)?;
    Ok(sort_out_possible_values(values))
}

fn parse_days_of_month(input: &mut &str) -> PResult<PossibleLiterals> {
    let values = alt((
        parse_asterisk_with_range(1..=31),
        parse_single_number_in_range(1..=31).map(|n| vec![PossibleValue::Literal(n)]),
    ))
    .parse_next(input)?;
    Ok(sort_out_possible_values(values))
}

fn parse_timezone(input: &mut &str) -> PResult<jiff::tz::TimeZone> {
    take_while(0.., |_| true)
        .try_map(|timezone| {
            jiff::tz::TimeZone::get(timezone).map_err(|_| {
                StringContext(format!(
                    "failed to find timezone {timezone}; \
                for a list of time zones, see the list of tz database time zones on Wikipedia: \
                https://en.wikipedia.org/wiki/List_of_tz_database_time_zones#List"
                ))
            })
        })
        .parse_next(input)
}

fn parse_asterisk_with_range<'a>(
    range: RangeInclusive<u8>,
) -> impl Parser<&'a str, Vec<PossibleValue>, ContextError> {
    literal("*").map(move |_| range.clone().map(PossibleValue::Literal).collect())
}

fn parse_single_number_in_range<'a>(
    range: RangeInclusive<u8>,
) -> impl Parser<&'a str, u8, ContextError> {
    dec_uint.try_map(move |n| {
        if range.contains(&n) {
            Ok(n)
        } else {
            Err(StringContext(format!(
                "value must be in range {range:?}; found {n}"
            )))
        }
    })
}

#[cfg(test)]
mod tests {
    use insta::assert_debug_snapshot;
    use insta::assert_snapshot;

    use super::*;
    use crate::setup_logging;

    #[test]
    fn test_parse_crontab() {
        setup_logging();

        assert_debug_snapshot!(parse_crontab("* * * * * Asia/Shanghai").unwrap());
        assert_debug_snapshot!(parse_crontab("2 4 * * * Asia/Shanghai").unwrap());
        assert_snapshot!(parse_crontab("invalid 4 * * * Asia/Shanghai").unwrap_err());
        assert_snapshot!(parse_crontab("* * * * * Unknown/Timezone").unwrap_err());
    }
}
