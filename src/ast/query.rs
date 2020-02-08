// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

/// The most complete variant of a `SELECT` query expression, optionally
/// including `WITH`, `UNION` / other set operations, and `ORDER BY`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Query {
    /// WITH (common table expressions, or CTEs)
    pub ctes: Vec<Cte>,
    /// SELECT or UNION / EXCEPT / INTECEPT
    pub body: SetExpr,
    /// ORDER BY
    pub order_by: Vec<OrderByExpr>,
    /// `LIMIT { <N> | ALL }`
    pub limit: Option<Expr>,
    /// `OFFSET <N> { ROW | ROWS }`
    pub offset: Option<Expr>,
    /// `FETCH { FIRST | NEXT } <N> [ PERCENT ] { ROW | ROWS } | { ONLY | WITH TIES }`
    pub fetch: Option<Fetch>,
}

impl fmt::Display for Query {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.ctes.is_empty() {
            write!(f, "WITH {} ", display_comma_separated(&self.ctes))?;
        }
        write!(f, "{}", self.body)?;
        if !self.order_by.is_empty() {
            write!(f, " ORDER BY {}", display_comma_separated(&self.order_by))?;
        }
        if let Some(ref limit) = self.limit {
            write!(f, " LIMIT {}", limit)?;
        }
        if let Some(ref offset) = self.offset {
            write!(f, " OFFSET {} ROWS", offset)?;
        }
        if let Some(ref fetch) = self.fetch {
            write!(f, " {}", fetch)?;
        }
        Ok(())
    }
}

/// A node in a tree, representing a "query body" expression, roughly:
/// `SELECT ... [ {UNION|EXCEPT|INTERSECT} SELECT ...]`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SetExpr {
    /// Restricted SELECT .. FROM .. HAVING (no ORDER BY or set operations)
    Values(Values),
    // TODO: ANSI SQL supports `TABLE` here.
}

impl fmt::Display for SetExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            SetExpr::Values(v) => write!(f, "{}", v),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SetOperator {}

/// A single CTE (used after `WITH`): `alias [(col1, col2, ...)] AS ( query )`
/// The names in the column list before `AS`, when specified, replace the names
/// of the columns returned by the query. The parser does not validate that the
/// number of columns in the query matches the number of columns in the query.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Cte {
    pub alias: TableAlias,
    pub query: Query,
}

impl fmt::Display for Cte {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} AS ({})", self.alias, self.query)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TableAlias {
    pub name: Ident,
    pub columns: Vec<Ident>,
}

impl fmt::Display for TableAlias {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)?;
        if !self.columns.is_empty() {
            write!(f, " ({})", display_comma_separated(&self.columns))?;
        }
        Ok(())
    }
}

/// SQL ORDER BY expression
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OrderByExpr {
    pub expr: Expr,
    pub asc: Option<bool>,
}

impl fmt::Display for OrderByExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.asc {
            Some(true) => write!(f, "{} ASC", self.expr),
            Some(false) => write!(f, "{} DESC", self.expr),
            None => write!(f, "{}", self.expr),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Fetch {
    pub with_ties: bool,
    pub percent: bool,
    pub quantity: Option<Expr>,
}

impl fmt::Display for Fetch {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let extension = if self.with_ties { "WITH TIES" } else { "ONLY" };
        if let Some(ref quantity) = self.quantity {
            let percent = if self.percent { " PERCENT" } else { "" };
            write!(f, "FETCH FIRST {}{} ROWS {}", quantity, percent, extension)
        } else {
            write!(f, "FETCH FIRST ROWS {}", extension)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Top {
    /// SQL semantic equivalent of LIMIT but with same structure as FETCH.
    pub with_ties: bool,
    pub percent: bool,
    pub quantity: Option<Expr>,
}

impl fmt::Display for Top {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let extension = if self.with_ties { " WITH TIES" } else { "" };
        if let Some(ref quantity) = self.quantity {
            let percent = if self.percent { " PERCENT" } else { "" };
            write!(f, "TOP ({}){}{}", quantity, percent, extension)
        } else {
            write!(f, "TOP{}", extension)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Values(pub Vec<Vec<Expr>>);

impl fmt::Display for Values {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "VALUES ")?;
        let mut delim = "";
        for row in &self.0 {
            write!(f, "{}", delim)?;
            delim = ", ";
            write!(f, "({})", display_comma_separated(row))?;
        }
        Ok(())
    }
}
