import KRTheory

open KRTheory KRTheory.TransMon

/-! One `#print axioms` per milestone-terminal theorem. CI parses the
output and fails on any axiom outside {propext, Classical.choice,
Quot.sound} (spec §1 item 4). Extend this list as milestones land. -/

#print axioms regular_faithful
#print axioms StrongDivides.trans
#print axioms StrongDivides.wreath
#print axioms wreath_assoc_div
#print axioms wreathList_append
#print axioms bar_divides
#print axioms reset_split
#print axioms reset_div_flipFlops
