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

extern crate core;

use std::collections::BTreeSet;
use std::str::FromStr;

use jiff::tz::TimeZone;
use jiff::Span;
use jiff::Timestamp;
use jiff::ToSpan;
use jiff::Unit;
use jiff::Zoned;

mod parser;
pub use parser::parse_crontab;
pub use parser::ParseError;

#[derive(Debug, Clone, thiserror::Error)]
#[error("{0}")]
pub struct Error(String);

#[derive(Debug)]
pub struct Corntab {
    minutes: PossibleLiterals,
    hours: PossibleLiterals,
    months: PossibleLiterals,
    days_of_month: PossibleLiterals,
    days_of_week: PossibleLiterals,
    timezone: TimeZone,
}

#[derive(Debug)]
enum PossibleValue {
    Literal(u8),
    // TODO(tisonkun): work out whether these extensions are valuable
    //  https://en.wikipedia.org/wiki/Cron#Non-standard_characters
    //
    // NearestWeekday(u8),
    // LastDayOfWeek(Weekday),
    // NthDayOfWeek(u8, Weekday),
}

fn sort_out_possible_values(values: Vec<PossibleValue>) -> PossibleLiterals {
    let literals = values
        .into_iter()
        .map(|value| match value {
            PossibleValue::Literal(value) => value,
        })
        .collect();
    PossibleLiterals { values: literals }
}

#[derive(Debug)]
struct PossibleLiterals {
    values: BTreeSet<u8>,
}

impl PossibleLiterals {
    fn matches(&self, value: u8) -> bool {
        self.values.contains(&value)
    }
}

impl FromStr for Corntab {
    type Err = ParseError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        parse_crontab(input)
    }
}

impl Corntab {
    pub fn find_next_timestamp_millis(&self, timestamp_millis: i64) -> Result<i64, Error> {
        Timestamp::from_millisecond(timestamp_millis)
            .map_err(time_error_with_context("failed to parse timestamp"))
            .and_then(|ts| self.find_next_timestamp(ts))
            .map(|ts| ts.as_millisecond())
    }

    pub fn find_next_timestamp(&self, timestamp: Timestamp) -> Result<Timestamp, Error> {
        let zoned = timestamp.to_zoned(self.timezone.clone());

        // checked at most 4 years to cover the leap year case
        let bound = &zoned + 4.years();

        // at least should be the next minutes
        let mut next = zoned;
        next = advance_time_and_round(next, 1.minute(), Some(Unit::Minute))?;

        loop {
            if next > bound {
                return Err(Error(format!(
                    "failed to find next timestamp in four years; end with {next}"
                )));
            }

            if !self.months.matches(next.month() as u8) {
                let rest_days = next.days_in_month() - next.day() + 1;
                next = advance_time_and_round(next, rest_days.days(), Some(Unit::Day))?;
                continue;
            }

            if !self.days_of_month.matches(next.day() as u8) {
                next = advance_time_and_round(next, 1.day(), Some(Unit::Day))?;
                continue;
            }

            if !self.days_of_week.matches(next.weekday() as u8) {
                next = advance_time_and_round(next, 1.day(), Some(Unit::Day))?;
                continue;
            }

            if !self.hours.matches(next.hour() as u8) {
                next = advance_time_and_round(next, 1.hour(), Some(Unit::Hour))?;
                continue;
            }

            if !self.minutes.matches(next.minute() as u8) {
                next = advance_time_and_round(next, 1.minute(), Some(Unit::Minute))?;
                continue;
            }

            break Ok(next.timestamp());
        }
    }
}

fn advance_time_and_round(zoned: Zoned, span: Span, unit: Option<Unit>) -> Result<Zoned, Error> {
    let mut next = zoned;

    next = next
        .checked_add(span)
        .map_err(time_error_with_context(&format!(
            "failed to advance timestamp; end with {next}"
        )))?;

    if let Some(unit) = unit {
        next = next.round(unit).map_err(time_error_with_context(&format!(
            "failed to round timestamp; end with {next}"
        )))?;
    }

    Ok(next)
}

fn time_error_with_context(context: &str) -> impl FnOnce(jiff::Error) -> Error + '_ {
    move |error| Error(format!("{context}: {error}"))
}

#[cfg(test)]
fn setup_logging() {
    use logforth::append;
    use logforth::filter::EnvFilter;
    use logforth::layout::TextLayout;
    use logforth::Dispatch;
    use logforth::Logger;

    static SETUP_LOGGING: std::sync::Once = std::sync::Once::new();
    SETUP_LOGGING.call_once(|| {
        Logger::new()
            .dispatch(
                Dispatch::new()
                    .filter(EnvFilter::from_default_env_or("DEBUG"))
                    .layout(TextLayout::default())
                    .append(append::Stderr),
            )
            .apply()
            .unwrap();
    });
}

#[cfg(test)]
mod tests {
    use jiff::Timestamp;

    use crate::setup_logging;
    use crate::Corntab;

    #[test]
    fn test_find_next() {
        setup_logging();

        let crontab = "0 0 1 1 * Asia/Shanghai".parse::<Corntab>().unwrap();
        let timestamp = Timestamp::now();
        let next = crontab.find_next_timestamp(timestamp).unwrap();
        println!("next: {}", next.to_zoned(crontab.timezone.clone()));
    }
}
