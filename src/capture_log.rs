use log::{Level, Log, Metadata, Record};
use std::sync::{Arc, Mutex};

#[derive(Debug, Default)]
pub struct LogInner {
    lines: Vec<String>,
}

impl LogInner {
    fn write(&mut self, line: String) {
        self.lines.push(line);
    }

    pub fn get_lines(&mut self) -> Vec<String> {
        let new_lines = Vec::new();
        std::mem::replace(&mut self.lines, new_lines)
    }
}

pub struct CaptureLogger {
    print_level: Level,
    inner: Arc<Mutex<LogInner>>,
    results: Arc<Mutex<Vec<String>>>,
}

impl Log for CaptureLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= self.print_level
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            let mut line = String::new();
            line.push_str(&format!(
                "{}:{}:{}: ",
                record.file().unwrap(),
                record.line().unwrap(),
                record.level()
            ));
            line.push_str(&format!("{}", record.args()));
            self.msg(line);
        }
    }

    fn flush(&self) {
        // Move the lines into the results vector
        let mut results = self.results.lock().unwrap();
        let mut inner = self.inner.lock().unwrap();

        // FIXME: move rather than clone
        results.append(&mut inner.lines);
    }
}

impl CaptureLogger {
    pub fn new(lvl: Level) -> (Self, Arc<Mutex<LogInner>>) {
        let inner = Arc::new(Mutex::new(LogInner::default()));
        (
            CaptureLogger {
                print_level: lvl,
                inner: inner.clone(),
                results: Arc::new(Mutex::new(Vec::new())),
            },
            inner,
        )
    }

    pub fn msg(&self, line: String) {
        eprintln!("{}", line);

        let mut inner = self.inner.lock().unwrap();
        inner.write(line);
    }
}

//-------------------------------
