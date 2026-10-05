import OIO.Proofs

/-!
# Kernel Verification Audit (`OIO.Audit`)

Prints the foundational principles depended upon by every top-level theorem and lemma in `OIO.Proofs`.
All declarations should depend only on `[propext, Classical.choice, Quot.sound]`.
-/

#print axioms oio_all_results
#print axioms thm_causality
#print axioms lem_wellposed
#print axioms rem_cost_counts
#print axioms lem_path
#print axioms lem_ledger
#print axioms lem_lifetime
#print axioms lem_potential
#print axioms thm_rvm
#print axioms cor_oilo
#print axioms rem_stall
#print axioms prop_small
