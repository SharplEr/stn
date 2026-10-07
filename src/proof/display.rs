//! Human-readable compositions, separate from the typed evidence used by the checker.
use super::{ProofId, ProofNode, ProofStore, Rule};
use indexmap::IndexMap;
use std::fmt;

/// Preferred width of a feature definition, including its report indentation.
const DEFINITION_WIDTH: usize = 100;

impl ProofStore {
    /// Format a well-formed witness as a left-to-right composition without types.
    /// Composition is associative; fanout grouping and unary-rule scope are preserved.
    /// Shared premises appear at every occurrence in the unfolded expression.
    pub fn expression(&self, id: ProofId) -> String {
        ProofExpression { store: self, id }.to_string()
    }

    /// Print distinct displayed compositions in witness order, grouping identical
    /// text at the same cost. The underlying typed witnesses remain separate.
    pub(crate) fn write_alternatives(
        &self,
        f: &mut fmt::Formatter<'_>,
        name: &str,
        roots: &[ProofId],
    ) -> fmt::Result {
        let mut alternatives = IndexMap::new();
        for &id in roots {
            let definition = ProofExpression { store: self, id }.definition(name);
            *alternatives
                .entry((self[id].cost, definition))
                .or_insert(0usize) += 1;
        }
        let multiple = alternatives.len() > 1;
        for (index, ((cost, definition), count)) in alternatives.into_iter().enumerate() {
            if index > 0 {
                writeln!(f)?;
            }
            if multiple {
                writeln!(f, "  alternative {} ({count} witness(es)):", index + 1)?;
            }
            writeln!(
                f,
                "  cost: functions={}, rules={}",
                cost.functions, cost.rules
            )?;
            writeln!(f, "{definition}")?;
        }
        Ok(())
    }
}

/// Borrowed view of a proof graph for rendering an expression or a feature definition.
/// Alternate display breaks only the outer pipeline, keeping nested rule scopes intact.
struct ProofExpression<'a> {
    /// Graph owning the root and all its premises.
    store: &'a ProofStore,
    /// Root of the expression being displayed.
    id: ProofId,
}

impl ProofExpression<'_> {
    /// Keep short definitions on one line; lay out long pipelines in execution order.
    fn definition(&self, name: &str) -> String {
        let inline = format!("  {name} = {self}");
        if inline.chars().count() <= DEFINITION_WIDTH || self.composition(self.id).is_none() {
            return inline;
        }
        format!("  {name} =\n      {self:#}")
    }

    /// A valid binary composition can be flattened without changing its meaning.
    fn composition(&self, id: ProofId) -> Option<(ProofId, ProofId)> {
        match &self.store[id].node {
            ProofNode::Inference {
                rule: Rule::Compose,
                children,
            } => match children.as_slice() {
                &[left, right] => Some((left, right)),
                _ => None,
            },
            _ => None,
        }
    }

    /// Traverse either association of a composition in execution order. Fanout remains
    /// one parenthesized step; pipelines inside unary rules use their own separators.
    fn pipeline(&self, f: &mut fmt::Formatter<'_>, id: ProofId, separator: &str) -> fmt::Result {
        if let Some((left, right)) = self.composition(id) {
            self.pipeline(f, left, separator)?;
            f.write_str(separator)?;
            self.pipeline(f, right, separator)
        } else {
            self.operand(f, id)
        }
    }

    /// Parenthesize binary operands explicitly, including nested fanouts: ordered
    /// products do not associate, and a branch may itself contain a pipeline.
    fn operand(&self, f: &mut fmt::Formatter<'_>, id: ProofId) -> fmt::Result {
        let binary = matches!(
            &self.store[id].node,
            ProofNode::Inference { rule: Rule::Compose | Rule::Fanout, children }
                if children.len() == 2
        );
        if binary {
            f.write_str("(")?;
        }
        self.node(f, id)?;
        if binary {
            f.write_str(")")?;
        }
        Ok(())
    }

    /// Render structural rules explicitly. Unexpected arities use ordinary call
    /// syntax so the checker can also format a malformed node in an error message.
    fn node(&self, f: &mut fmt::Formatter<'_>, id: ProofId) -> fmt::Result {
        let (rule, children) = match &self.store[id].node {
            ProofNode::Primitive { name, .. } => return f.write_str(name),
            ProofNode::Inference { rule, children } => (rule, children),
        };
        match (rule, children.as_slice()) {
            (Rule::Compose, [_, _]) => self.pipeline(f, id, " >>> "),
            (Rule::Fanout, [left, right]) => {
                self.operand(f, *left)?;
                f.write_str(" &&& ")?;
                self.operand(f, *right)
            }
            _ => {
                match rule {
                    Rule::ExtendSum => f.write_str("extend")?,
                    _ => write!(f, "{rule}")?,
                }
                if !children.is_empty() {
                    f.write_str("(")?;
                    for (index, &child) in children.iter().enumerate() {
                        if index > 0 {
                            f.write_str(", ")?;
                        }
                        self.node(f, child)?;
                    }
                    f.write_str(")")?;
                }
                Ok(())
            }
        }
    }
}

impl fmt::Display for ProofExpression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() && self.composition(self.id).is_some() {
            self.pipeline(f, self.id, "\n      >>> ")
        } else {
            self.node(f, self.id)
        }
    }
}
