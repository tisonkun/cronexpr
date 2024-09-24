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

//! # Crontab
//!
//! A library to parse and drive the crontab expression.
//!
//! Here is a quick example that shows how to parse a cron expression and drive it with a timestamp:
//!
//!```rust
//! let crontab = cronexpr::parse_crontab("2 4 * * * Asia/Shanghai").unwrap();
//! assert_eq!(
//!     crontab
//!         .find_next("2024-09-24T10:06:52+08:00")
//!         .unwrap()
//!         .to_string(),
//!     "2024-09-25T04:02:00+08:00[Asia/Shanghai]"
//! );
//!
//! let driver = crontab
//!     .drive("2024-09-24T10:06:52+08:00", None::<cronexpr::MakeTimestamp>)
//!     .unwrap();
//!
//! assert_eq!(
//!     driver
//!         .take(5)
//!         .map(|ts| ts.map(|ts| ts.to_string()))
//!         .collect::<Result<Vec<_>, cronexpr::Error>>()
//!         .unwrap(),
//!     vec![
//!         "2024-09-25T04:02:00+08:00[Asia/Shanghai]",
//!         "2024-09-26T04:02:00+08:00[Asia/Shanghai]",
//!         "2024-09-27T04:02:00+08:00[Asia/Shanghai]",
//!         "2024-09-28T04:02:00+08:00[Asia/Shanghai]",
//!         "2024-09-29T04:02:00+08:00[Asia/Shanghai]",
//!     ]
//! );
//!
//! let driver = crontab
//!     .drive(
//!         "2024-09-24T10:06:52+08:00",
//!         Some("2024-10-01T00:00:00+08:00"),
//!     )
//!     .unwrap();
//! assert_eq!(
//!     driver
//!         .map(|ts| ts.map(|ts| ts.to_string()))
//!         .collect::<Result<Vec<_>, cronexpr::Error>>()
//!         .unwrap(),
//!     vec![
//!         "2024-09-25T04:02:00+08:00[Asia/Shanghai]",
//!         "2024-09-26T04:02:00+08:00[Asia/Shanghai]",
//!         "2024-09-27T04:02:00+08:00[Asia/Shanghai]",
//!         "2024-09-28T04:02:00+08:00[Asia/Shanghai]",
//!         "2024-09-29T04:02:00+08:00[Asia/Shanghai]",
//!         "2024-09-30T04:02:00+08:00[Asia/Shanghai]",
//!     ]
//! );
//! ```

use std::collections::BTreeSet;
use std::collections::HashSet;
use std::str::FromStr;

use jiff::civil::Weekday;
use jiff::tz::TimeZone;
use jiff::RoundMode;
use jiff::Span;
use jiff::Timestamp;
use jiff::ToSpan;
use jiff::Unit;
use jiff::Zoned;
use jiff::ZonedRound;

mod parser;
pub use parser::normalize_crontab;
pub use parser::parse_crontab;

/// An error that can occur in this crate.
#[derive(Debug, Clone, thiserror::Error)]
#[error("{0}")]
pub struct Error(String);

/// A data struct representing the crontab expression.
#[derive(Debug, Clone)]
pub struct Crontab {
    minutes: PossibleLiterals,
    hours: PossibleLiterals,
    months: PossibleLiterals,
    days_of_month: ParsedDaysOfMonth,
    days_of_week: ParsedDaysOfWeek,
    timezone: TimeZone,
}

#[derive(Debug)]
enum PossibleValue {
    /// Literally match the value.
    ///
    /// For example, a possible literal of minute '15' matches when the minute is '15'.
    Literal(u8),
    /// Parsed from '<day>W' in day-of-month field.
    ///
    /// The 'W' character is allowed for the day-of-month field. This character is used to specify
    /// the weekday (Monday-Friday) nearest the given day. As an example, if "15W" is specified as
    /// the value for the day-of-month field, the meaning is: "the nearest weekday to the 15th of
    /// the month." So, if the 15th is a Saturday, the trigger fires on Friday the 14th. If the
    /// 15th is a Sunday, the trigger fires on Monday the 16th. If the 15th is a Tuesday, then it
    /// fires on Tuesday the 15th. However, if "1W" is specified as the value for day-of-month, and
    /// the 1st is a Saturday, the trigger fires on Monday the 3rd, as it does not 'jump' over the
    /// boundary of a month's days. The 'W' character can be specified only when the day-of-month
    /// is a single day, not a range or list of days.
    NearestWeekday(u8),
    /// Parsed from '<day>L' in day-of-month field.
    ///
    /// 'L' stands for "last". When used in the day-of-month field, it specifies the last day of
    /// the month.
    LastDayOfMonth,
    /// Parsed from '<weekday>L' in day-of-week field.
    ///
    /// 'L' stands for "last". When used in the day-of-week field, it allows specifying constructs
    /// such as "the last Friday" ("5L") of a given month.
    LastDayOfWeek(Weekday),
    /// Parsed from '<weekday>#<nth>' in day-of-week field.
    ///
    /// '#' is allowed for the day-of-week field, and must be followed by a number between one and
    /// five. It allows specifying constructs such as "the second Friday" of a given month. For
    /// example, entering "5#3" in the day-of-week field corresponds to the third Friday of every
    /// month.
    NthDayOfWeek(u8, Weekday),
}

/// @see [PossibleValue::Literal]
#[derive(Debug, Clone)]
struct PossibleLiterals {
    values: BTreeSet<u8>,
}

impl PossibleLiterals {
    fn matches(&self, value: u8) -> bool {
        self.values.contains(&value)
    }
}

#[derive(Debug, Clone)]
struct ParsedDaysOfWeek {
    /// @see [PossibleValue::Literal]
    literals: BTreeSet<u8>,
    /// @see [PossibleValue::LastDayOfWeek]
    last_days_of_week: HashSet<Weekday>,
    /// @see [PossibleValue::NthDayOfWeek]
    nth_days_of_week: HashSet<(u8, Weekday)>,

    // to implement Vixie's cron behavior
    // ref - https://crontab.guru/cron-bug.html
    start_with_asterisk: bool,
}

impl ParsedDaysOfWeek {
    fn matches(&self, value: &Zoned) -> bool {
        if self.literals.contains(&(value.weekday() as u8)) {
            return true;
        }

        for weekday in self.last_days_of_week.iter() {
            if value.weekday() != *weekday {
                continue;
            }

            if (value + 1.week()).month() > value.month() {
                return true;
            }
        }

        for (nth, weekday) in self.nth_days_of_week.iter() {
            if value.weekday() != *weekday {
                continue;
            }

            if let Ok(nth_weekday) = value.nth_weekday_of_month(*nth as i8, *weekday) {
                if nth_weekday.date() == value.date() {
                    return true;
                }
            }
        }

        false
    }
}

#[derive(Debug, Clone)]
struct ParsedDaysOfMonth {
    /// @see [PossibleValue::Literal]
    literals: BTreeSet<u8>,
    /// @see [PossibleValue::LastDayOfMonth]
    last_day_of_month: bool,
    /// @see [PossibleValue::NearestWeekday]
    nearest_weekdays: BTreeSet<u8>,

    // to implement Vixie's cron behavior
    // ref - https://crontab.guru/cron-bug.html
    start_with_asterisk: bool,
}

impl ParsedDaysOfMonth {
    fn matches(&self, value: &Zoned) -> bool {
        if self.literals.contains(&(value.day() as u8)) {
            return true;
        }

        if self.last_day_of_month && (value + 1.day()).month() > value.month() {
            return true;
        }

        for day in self.nearest_weekdays.iter() {
            let day = *day as i8;

            match value.weekday() {
                // 'nearest weekday' matcher can never match weekends
                Weekday::Saturday | Weekday::Sunday => {
                    continue;
                }
                // if today is Tuesday, Wednesday, or Thursday, only if the day matches today can
                // today be the nearest weekday
                Weekday::Tuesday | Weekday::Wednesday | Weekday::Thursday => {
                    if value.day() == day {
                        return true;
                    }
                }
                Weekday::Monday => {
                    // if the day matches today, today is the nearest weekday
                    if value.day() == day {
                        return true;
                    }

                    // matches the last Sunday
                    if value.day() - 1 == day {
                        return true;
                    }

                    // matches the edge case: 1W and the 1st is Saturday
                    if value.day() == 3 && day == 1 {
                        return true;
                    }
                }
                Weekday::Friday => {
                    // if the day matches today, today is the nearest weekday
                    if value.day() == day {
                        return true;
                    }

                    let last_day_of_this_month = value.days_in_month();

                    // matches the next Saturday
                    if value.day() + 1 == day && day <= last_day_of_this_month {
                        return true;
                    }

                    // matches the edge case: last day of month is Sunday
                    if value.day() + 2 == day && day == last_day_of_this_month {
                        return true;
                    }
                }
            }
        }

        false
    }
}

impl FromStr for Crontab {
    type Err = Error;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        parse_crontab(input)
    }
}

impl<'a> TryFrom<&'a str> for Crontab {
    type Error = Error;

    fn try_from(input: &'a str) -> Result<Self, Self::Error> {
        FromStr::from_str(input)
    }
}

/// A helper struct to construct a [`Timestamp`].
///
/// This is useful to avoid version lock-in to [`jiff`].
#[derive(Debug, Copy, Clone)]
pub struct MakeTimestamp(Timestamp);

impl From<Timestamp> for MakeTimestamp {
    fn from(timestamp: Timestamp) -> Self {
        MakeTimestamp(timestamp)
    }
}

impl FromStr for MakeTimestamp {
    type Err = Error;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        Timestamp::from_str(input)
            .map(MakeTimestamp)
            .map_err(error_with_context("failed to parse timestamp"))
    }
}

impl<'a> TryFrom<&'a str> for MakeTimestamp {
    type Error = Error;

    fn try_from(input: &'a str) -> Result<Self, Self::Error> {
        FromStr::from_str(input)
    }
}

impl MakeTimestamp {
    /// Creates a new instant in time from the number of seconds elapsed since the Unix epoch.
    ///
    /// See [`Timestamp::from_second`] for more details.
    pub fn from_second(second: i64) -> Result<Self, Error> {
        Timestamp::from_second(second)
            .map(MakeTimestamp)
            .map_err(error_with_context("failed to make timestamp"))
    }

    /// Creates a new instant in time from the number of milliseconds elapsed since the Unix epoch.
    ///
    /// See [`Timestamp::from_millisecond`] for more details.
    pub fn from_millisecond(millisecond: i64) -> Result<Self, Error> {
        Timestamp::from_millisecond(millisecond)
            .map(MakeTimestamp)
            .map_err(error_with_context("failed to make timestamp"))
    }

    /// Creates a new instant in time from the number of microseconds elapsed since the Unix epoch.
    ///
    /// See [`Timestamp::from_microsecond`] for more details.
    pub fn from_microsecond(microsecond: i64) -> Result<Self, Error> {
        Timestamp::from_microsecond(microsecond)
            .map(MakeTimestamp)
            .map_err(error_with_context("failed to make timestamp"))
    }

    /// Creates a new instant in time from the number of nanoseconds elapsed since the Unix epoch.
    ///
    /// See [`Timestamp::from_nanosecond`] for more details.
    pub fn from_nanosecond(nanosecond: i128) -> Result<Self, Error> {
        Timestamp::from_nanosecond(nanosecond)
            .map(MakeTimestamp)
            .map_err(error_with_context("failed to make timestamp"))
    }
}

impl Crontab {
    /// Create an iterator over next timestamps within `(start, end)`.
    ///
    /// If `end` is `None`, the iteration is infinite. Otherwise, the iteration stops when the
    /// next timestamp is equal to or beyond the `end` timestamp.
    ///
    /// # Errors
    ///
    /// This returns an error if fail to make timestamp from the input of `start` or `end`.
    ///
    /// For more usages, see [the top-level documentation][crate].
    pub fn drive<T1, T2>(&self, start: T1, end: Option<T2>) -> Result<Driver, Error>
    where
        T1: TryInto<MakeTimestamp>,
        T1::Error: std::error::Error,
        T2: TryInto<MakeTimestamp>,
        T2::Error: std::error::Error,
    {
        let start = start
            .try_into()
            .map_err(error_with_context("failed to parse start timestamp"))?
            .0;

        let end = match end {
            Some(end) => Some(
                end.try_into()
                    .map_err(error_with_context("failed to parse end timestamp"))?
                    .0,
            ),
            None => None,
        };

        Ok(Driver {
            crontab: self.clone(),
            timestamp: start,
            bound: end,
        })
    }

    /// Find the next timestamp after the given timestamp.
    ///
    /// # Errors
    ///
    /// This returns an error if fail to make timestamp from the input `timestamp`.
    ///
    /// For more usages, see [the top-level documentation][crate].
    pub fn find_next<T>(&self, timestamp: T) -> Result<Zoned, Error>
    where
        T: TryInto<MakeTimestamp>,
        T::Error: std::error::Error,
    {
        let zoned = timestamp
            .try_into()
            .map(|ts| ts.0.to_zoned(self.timezone.clone()))
            .map_err(error_with_context("failed to parse timestamp"))?;

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

            // implement Vixie's cron bug: https://crontab.guru/cron-bug.html
            if self.days_of_month.start_with_asterisk || self.days_of_week.start_with_asterisk {
                // 1. use intersection if any of the two fields start with '*'
                let cond = self.days_of_month.matches(&next) && self.days_of_week.matches(&next);
                if !cond {
                    next = advance_time_and_round(next, 1.day(), Some(Unit::Day))?;
                    continue;
                }
            } else {
                // 2. otherwise, use union
                let cond = self.days_of_month.matches(&next) && self.days_of_week.matches(&next);
                if !cond {
                    next = advance_time_and_round(next, 1.day(), Some(Unit::Day))?;
                    continue;
                }
            }

            if !self.hours.matches(next.hour() as u8) {
                next = advance_time_and_round(next, 1.hour(), Some(Unit::Hour))?;
                continue;
            }

            if !self.minutes.matches(next.minute() as u8) {
                next = advance_time_and_round(next, 1.minute(), Some(Unit::Minute))?;
                continue;
            }

            break Ok(next);
        }
    }
}

/// Iterator over next timestamps. See [Crontab::drive] for more details.
#[derive(Debug)]
pub struct Driver {
    /// The crontab to find the next timestamp.
    crontab: Crontab,
    /// The current timestamp; mutable.
    timestamp: Timestamp,
    /// When next timestamp is beyond this bound, stop iteration. [`None`] if never stop.
    bound: Option<Timestamp>,
}

impl Iterator for Driver {
    type Item = Result<Zoned, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        let zoned = match self.crontab.find_next(self.timestamp) {
            Ok(zoned) => zoned,
            Err(err) => return Some(Err(err)),
        };

        if let Some(bound) = self.bound {
            if zoned.timestamp() >= bound {
                return None;
            }
        }

        self.timestamp = zoned.timestamp();

        Some(Ok(zoned))
    }
}

fn advance_time_and_round(zoned: Zoned, span: Span, unit: Option<Unit>) -> Result<Zoned, Error> {
    let mut next = zoned;

    next = next.checked_add(span).map_err(error_with_context(&format!(
        "failed to advance timestamp; end with {next}"
    )))?;

    if let Some(unit) = unit {
        next = next
            .round(ZonedRound::new().mode(RoundMode::Trunc).smallest(unit))
            .map_err(error_with_context(&format!(
                "failed to round timestamp; end with {next}"
            )))?;
    }

    Ok(next)
}

fn error_with_context<E: std::error::Error>(context: &str) -> impl FnOnce(E) -> Error + '_ {
    move |error| Error(format!("{context}: {error}"))
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use insta::assert_snapshot;
    use jiff::Zoned;

    use crate::Crontab;
    use crate::Driver;
    use crate::MakeTimestamp;

    fn make_driver(crontab: &str, timestamp: &str) -> Driver {
        let crontab = Crontab::from_str(crontab).unwrap();
        crontab.drive(timestamp, None::<MakeTimestamp>).unwrap()
    }

    fn drive(driver: &mut Driver) -> Zoned {
        driver.next().unwrap().unwrap()
    }

    #[test]
    fn test_next_timestamp() {
        let mut driver = make_driver("0 0 1 1 * Asia/Shanghai", "2024-01-01T00:00:00+08:00");
        assert_snapshot!(drive(&mut driver), @"2025-01-01T00:00:00+08:00[Asia/Shanghai]");

        let mut driver = make_driver("2 4 * * * Asia/Shanghai", "2024-09-11T19:08:35+08:00");
        assert_snapshot!(drive(&mut driver), @"2024-09-12T04:02:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-09-13T04:02:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-09-14T04:02:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-09-15T04:02:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-09-16T04:02:00+08:00[Asia/Shanghai]");

        let mut driver = make_driver("0 0 31 * * Asia/Shanghai", "2024-09-11T19:08:35+08:00");
        assert_snapshot!(drive(&mut driver), @"2024-10-31T00:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-12-31T00:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-01-31T00:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-03-31T00:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-05-31T00:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-07-31T00:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-08-31T00:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-10-31T00:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-12-31T00:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2026-01-31T00:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2026-03-31T00:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2026-05-31T00:00:00+08:00[Asia/Shanghai]");

        let mut driver = make_driver("0 18 * * 1-5 Asia/Shanghai", "2024-09-11T19:08:35+08:00");
        assert_snapshot!(drive(&mut driver), @"2024-09-12T18:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-09-13T18:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-09-16T18:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-09-17T18:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-09-18T18:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-09-19T18:00:00+08:00[Asia/Shanghai]");

        let mut driver = make_driver("0 18 * * TUE#1 Asia/Shanghai", "2024-09-24T00:08:35+08:00");
        assert_snapshot!(drive(&mut driver), @"2024-10-01T18:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-11-05T18:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-12-03T18:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-01-07T18:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-02-04T18:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-03-04T18:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-04-01T18:00:00+08:00[Asia/Shanghai]");

        let mut driver = make_driver("4 2 * * 1L Asia/Shanghai", "2024-09-24T00:08:35+08:00");
        assert_snapshot!(drive(&mut driver), @"2024-09-30T02:04:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-10-28T02:04:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-11-25T02:04:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-01-27T02:04:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-02-24T02:04:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-03-31T02:04:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-04-28T02:04:00+08:00[Asia/Shanghai]");

        let mut driver = make_driver("0 18 * * FRI#5 Asia/Shanghai", "2024-09-24T00:08:35+08:00");
        assert_snapshot!(drive(&mut driver), @"2024-11-29T18:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-01-31T18:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-05-30T18:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-08-29T18:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-10-31T18:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2026-01-30T18:00:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2026-05-29T18:00:00+08:00[Asia/Shanghai]");

        let mut driver = make_driver(
            "3 11 L JAN-FEB,5 * Asia/Shanghai",
            "2024-09-24T00:08:35+08:00",
        );
        assert_snapshot!(drive(&mut driver), @"2025-01-31T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-02-28T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-05-31T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2026-01-31T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2026-02-28T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2026-05-31T11:03:00+08:00[Asia/Shanghai]");

        let mut driver = make_driver("3 11 17W,L * * Asia/Shanghai", "2024-09-24T00:08:35+08:00");
        assert_snapshot!(drive(&mut driver), @"2024-09-30T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-10-17T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-10-31T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-11-18T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-11-30T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-12-17T11:03:00+08:00[Asia/Shanghai]");

        let mut driver = make_driver("3 11 1W * * Asia/Shanghai", "2024-09-24T00:08:35+08:00");
        assert_snapshot!(drive(&mut driver), @"2024-10-01T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-11-01T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-12-02T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-01-01T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-02-03T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-03-03T11:03:00+08:00[Asia/Shanghai]");

        let mut driver = make_driver("3 11 31W * * Asia/Shanghai", "2024-09-24T00:08:35+08:00");
        assert_snapshot!(drive(&mut driver), @"2024-10-31T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2024-12-31T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-01-31T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-03-31T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-05-30T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-07-31T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-08-29T11:03:00+08:00[Asia/Shanghai]");
        assert_snapshot!(drive(&mut driver), @"2025-10-31T11:03:00+08:00[Asia/Shanghai]");
    }
}
