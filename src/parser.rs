use std::collections::BTreeSet;
use std::fmt;
use std::ops::RangeBounds;

use winnow::ascii::digit1;
use winnow::combinator::alt;
use winnow::combinator::cut_err;
use winnow::error::ContextError;
use winnow::token::literal;
use winnow::token::take_while;
use winnow::PResult;
use winnow::Parser;

use crate::Corntab;
use crate::DayOfMonthExpr;
use crate::DayOfWeekExpr;
use crate::HourExpr;
use crate::MinuteExpr;
use crate::MonthExpr;

#[derive(Debug, Clone, thiserror::Error)]
#[error("{0}")]
pub struct ParseError(String);

#[derive(Debug, Clone, thiserror::Error)]
#[error("{0}")]
struct StringContext(String);

pub fn parse_crontab(input: &str) -> Result<Corntab, ParseError> {
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

    Ok(Corntab {
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
        "unexpected character"
    } else {
        &error
    };

    ParseError(format!("{context}:\n{input}\n{indent}^ {error}"))
}

fn parse_minutes(input: &mut &str) -> PResult<MinuteExpr> {
    fn match_asterisk(input: &mut &str) -> PResult<MinuteExpr> {
        literal("*").parse_next(input).map(|_| MinuteExpr::Asterisk)
    }

    fn match_single_number(input: &mut &str) -> PResult<MinuteExpr> {
        parse_single_number_in_range(input, 0..=59)
            .map(|minute| MinuteExpr::PossibleValues(BTreeSet::from_iter(vec![minute])))
    }

    alt((match_asterisk, match_single_number)).parse_next(input)
}

fn parse_hours(input: &mut &str) -> PResult<HourExpr> {
    fn match_asterisk(input: &mut &str) -> PResult<HourExpr> {
        literal("*").parse_next(input).map(|_| HourExpr::Asterisk)
    }

    fn match_single_number(input: &mut &str) -> PResult<HourExpr> {
        parse_single_number_in_range(input, 0..=23)
            .map(|hour| HourExpr::PossibleValues(BTreeSet::from_iter(vec![hour])))
    }

    alt((match_asterisk, match_single_number)).parse_next(input)
}

fn parse_months(input: &mut &str) -> PResult<MonthExpr> {
    fn match_asterisk(input: &mut &str) -> PResult<MonthExpr> {
        literal("*").parse_next(input).map(|_| MonthExpr::Asterisk)
    }

    fn match_single_number(input: &mut &str) -> PResult<MonthExpr> {
        parse_single_number_in_range(input, 1..=12)
            .map(|month| MonthExpr::PossibleValues(BTreeSet::from_iter(vec![month])))
    }

    alt((match_asterisk, match_single_number)).parse_next(input)
}

fn parse_days_of_week(input: &mut &str) -> PResult<DayOfWeekExpr> {
    fn match_asterisk(input: &mut &str) -> PResult<DayOfWeekExpr> {
        literal("*")
            .parse_next(input)
            .map(|_| DayOfWeekExpr::Asterisk)
    }

    fn match_single_number(input: &mut &str) -> PResult<DayOfWeekExpr> {
        parse_single_number_in_range(input, 0..=6).map(|day_of_week| {
            DayOfWeekExpr::PossibleValues(BTreeSet::from_iter(vec![day_of_week]))
        })
    }

    alt((match_asterisk, match_single_number)).parse_next(input)
}

fn parse_days_of_month(input: &mut &str) -> PResult<DayOfMonthExpr> {
    fn match_asterisk(input: &mut &str) -> PResult<DayOfMonthExpr> {
        literal("*")
            .parse_next(input)
            .map(|_| DayOfMonthExpr::Asterisk)
    }

    fn match_single_number(input: &mut &str) -> PResult<DayOfMonthExpr> {
        parse_single_number_in_range(input, 1..=31).map(|day_of_month| {
            DayOfMonthExpr::PossibleValues(BTreeSet::from_iter(vec![day_of_month]))
        })
    }

    alt((match_asterisk, match_single_number)).parse_next(input)
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

fn parse_single_number_in_range<Range>(input: &mut &str, range: Range) -> PResult<u8>
where
    Range: RangeBounds<u8> + fmt::Debug,
{
    let verifier = take_while(0.., |_| true).try_map(|n: &str| {
        let make_error = || StringContext(format!("value must be in range {range:?}; found {n}"));
        let n = n.parse::<u8>().map_err(|_| make_error())?;
        if range.contains(&n) {
            Ok(n)
        } else {
            Err(make_error())
        }
    });

    digit1.and_then(cut_err(verifier)).parse_next(input)
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

        assert_debug_snapshot!(parse_crontab("2 4 * * * Asia/Shanghai").unwrap());
        assert_snapshot!(parse_crontab("invalid 4 * * * Asia/Shanghai").unwrap_err());
        assert_snapshot!(parse_crontab("* * * * * Unknown/Timezone").unwrap_err());
    }
}
