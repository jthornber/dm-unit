use rusqlite::{params, Connection, Result};
use std::collections::BTreeMap;

#[derive(Debug)]
pub struct TestResult {
    pub pass: bool,
    pub log: String,

    // Risc V instruction count consumed by the test
    pub icount: u64,
}

pub struct TestResults {
    conn: Connection,
}

impl TestResults {
    pub fn new(path: &str) -> Result<Self> {
        let conn = Connection::open(path)?;
        Self::create_tables(&conn)?;
        Ok(Self { conn })
    }

    // FIXME: I don't think we need this, remove once confirmed
    fn commit(_conn: &Connection) -> Result<()> {
        //conn.execute("COMMIT", params![])?;
        Ok(())
    }

    fn create_tables(conn: &Connection) -> Result<()> {
        conn.execute(
            "CREATE TABLE IF NOT EXISTS result_sets (
                result_set_id INTEGER PRIMARY KEY,
                result_set TEXT UNIQUE
            )",
            params![],
        )?;

        conn.execute(
            "CREATE TABLE IF NOT EXISTS test_names (
                test_name_id INTEGER PRIMARY KEY,
                test_name TEXT UNIQUE
            )",
            params![],
        )?;

        conn.execute(
            "CREATE TABLE IF NOT EXISTS test_results (
                test_result_id INTEGER PRIMARY KEY,
                test_name_id INTEGER NOT NULL,
                pass BOOLEAN NOT NULL,
                log TEXT NOT NULL,
                result_set_id INTEGER NOT NULL,
                icount INTEGER NOT NULL,
                FOREIGN KEY (test_name_id) REFERENCES test_names(test_name_id),
                FOREIGN KEY (result_set_id) REFERENCES result_sets(result_set_id)
            )",
            params![],
        )?;

        Self::commit(conn)?;

        Ok(())
    }

    pub fn insert_test_result(
        &mut self,
        result_set: &str,
        test_name: &str,
        test_result: &TestResult,
    ) -> Result<()> {
        let test_name_id = self.get_or_insert_test_name(test_name)?;
        let result_set_id = self.get_or_insert_result_set(result_set)?;

        self.conn.execute(
            "INSERT INTO test_results (test_name_id, pass, log, result_set_id, icount)
             VALUES (?, ?, ?, ?, ?)",
            params![
                test_name_id,
                test_result.pass,
                test_result.log,
                result_set_id,
                test_result.icount,
            ],
        )?;

        Self::commit(&self.conn)?;
        Ok(())
    }

    pub fn get_or_insert_test_name(&mut self, test_name: &str) -> Result<i32> {
        let mut stmt = self
            .conn
            .prepare("SELECT test_name_id FROM test_names WHERE test_name = ?")?;
        let test_name_id = match stmt.query_row(params![test_name], |row| row.get(0)) {
            Ok(id) => id,
            Err(rusqlite::Error::QueryReturnedNoRows) => {
                self.conn.execute(
                    "INSERT INTO test_names (test_name) VALUES (?)",
                    params![test_name],
                )?;
                Self::commit(&self.conn)?;
                self.conn.last_insert_rowid() as i32
            }
            Err(err) => return Err(err),
        };

        Ok(test_name_id)
    }

    pub fn get_or_insert_result_set(&mut self, result_set: &str) -> Result<i32> {
        let mut stmt = self
            .conn
            .prepare("SELECT result_set_id FROM result_sets WHERE result_set = ?")?;
        let result_set_id = match stmt.query_row(params![result_set], |row| row.get(0)) {
            Ok(id) => id,
            Err(rusqlite::Error::QueryReturnedNoRows) => {
                self.conn.execute(
                    "INSERT INTO result_sets (result_set) VALUES (?)",
                    params![result_set],
                )?;
                Self::commit(&self.conn)?;

                self.conn.last_insert_rowid() as i32
            }
            Err(err) => return Err(err),
        };
        Ok(result_set_id)
    }

    /// Get the results for a given result set
    pub fn get_test_results(&self, result_set: &str) -> Result<BTreeMap<String, TestResult>> {
        let mut stmt = self.conn.prepare(
            "SELECT test_names.test_name, test_results.pass, test_results.log, test_results.icount
         FROM test_results
         JOIN test_names ON test_results.test_name_id = test_names.test_name_id
         JOIN result_sets ON test_results.result_set_id = result_sets.result_set_id
         WHERE result_sets.result_set = ?",
        )?;

        let rows = stmt
            .query_map(params![result_set], |row| {
                Ok((
                    row.get::<_, String>(0)?,
                    TestResult {
                        pass: row.get(1)?,
                        log: row.get(2)?,
                        icount: row.get(3)?,
                    },
                ))
            })
            .unwrap();

        let mut results = BTreeMap::new();
        for row in rows {
            let (test_name, test_result) = row.unwrap();
            results.insert(test_name, test_result);
        }

        Ok(results)
    }

    pub fn get_result_sets(&self) -> Result<Vec<String>> {
        let mut stmt = self.conn.prepare("SELECT result_set FROM result_sets")?;

        let rows = stmt
            .query_map(params![], |row| row.get::<_, String>(0))
            .unwrap();

        let mut results = Vec::new();
        for row in rows {
            results.push(row.unwrap());
        }

        Ok(results)
    }
}
