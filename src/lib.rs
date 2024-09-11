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
use jiff::Timestamp;

mod parser;
pub use parser::parse_crontab;
pub use parser::ParseError;

#[derive(Debug)]
pub struct Corntab {
    minutes: MinuteExpr,
    hours: HourExpr,
    days_of_month: DayOfMonthExpr,
    months: MonthExpr,
    days_of_week: DayOfWeekExpr,
    timezone: TimeZone,
}

#[derive(Debug)]
enum MinuteExpr {
    Asterisk,
    PossibleValues(BTreeSet<u8>),
}

#[derive(Debug)]
enum HourExpr {
    Asterisk,
    PossibleValues(BTreeSet<u8>),
}

#[derive(Debug)]
enum MonthExpr {
    Asterisk,
    PossibleValues(BTreeSet<u8>),
}

#[derive(Debug)]
enum DayOfWeekExpr {
    Asterisk,
    PossibleValues(BTreeSet<u8>),
}

#[derive(Debug)]
enum DayOfMonthExpr {
    Asterisk,
    PossibleValues(BTreeSet<u8>),
}

impl FromStr for Corntab {
    type Err = ParseError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        parse_crontab(input)
    }
}

impl Corntab {
    pub fn find_next_timestamp_millis(&self, timestamp_millis: i64) -> Result<i64, jiff::Error> {
        let timestamp = Timestamp::from_millisecond(timestamp_millis)?;
        Ok(self.find_next_timestamp(timestamp).as_millisecond())
    }

    pub fn find_next_timestamp(&self, timestamp: Timestamp) -> Timestamp {
        let zoned = timestamp.to_zoned(self.timezone.clone());
        dbg!(zoned).timestamp()
    }
}

#[cfg(test)]
fn setup_logging() {
    use logforth::append;
    use logforth::filter::EnvFilter;
    use logforth::layout::TextLayout;
    use logforth::Dispatch;
    use logforth::Logger;

    Logger::new()
        .dispatch(
            Dispatch::new()
                .filter(EnvFilter::from_default_env_or("DEBUG"))
                .layout(TextLayout::default())
                .append(append::Stderr),
        )
        .apply()
        .unwrap();
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use jiff::Timestamp;

    use crate::setup_logging;
    use crate::Corntab;

    #[test]
    fn test_find_next() {
        setup_logging();

        let crontab = "0 0 1 1 * Asia/Shanghai".parse::<Corntab>().unwrap();
        let timestamp = Timestamp::from_str("2024-01-01T00:00:00Z").unwrap();
        let next = crontab.find_next_timestamp(timestamp);
        // assert_eq!(next, Timestamp::from_str("2025-01-01T00:00:00Z").unwrap());
    }
}
