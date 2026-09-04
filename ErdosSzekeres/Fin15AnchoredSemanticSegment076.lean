module

public import ErdosSzekeres.Fin15AnchoredClauseChunk149
public import ErdosSzekeres.Fin15AnchoredClauseChunk150
public import ErdosSzekeres.Fin15AnchoredClauseChunk151

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 076. -/

theorem fin15Anchored_rejectSemanticSegment076
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom0679 chi) ∨
      ((Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom0684 chi) ∨
      (Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom0689 chi))) ∨
      (((Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom0789 chi) ∨
      (Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom1580 chi)) ∨
      ((¬Fin15AnchoredAtom2581 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom1580 chi) ∨
      (Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom0680 chi)))) ∨
      ((((Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom0682 chi) ∨
      (Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom0691 chi)) ∨
      ((Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom0791 chi) ∨
      (Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom1582 chi))) ∨
      (((¬Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom1582 chi) ∨
      (Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom0680 chi)) ∨
      ((Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom0683 chi) ∨
      (Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom0692 chi))))) ∨
      (((((Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom0792 chi) ∨
      (Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom1583 chi)) ∨
      ((¬Fin15AnchoredAtom2584 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom1583 chi) ∨
      (Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom0680 chi))) ∨
      (((Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom0684 chi) ∨
      (Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom0693 chi)) ∨
      ((Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom0793 chi) ∨
      (Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom1584 chi)))) ∨
      ((((¬Fin15AnchoredAtom2585 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom1584 chi) ∨
      (Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom0682 chi)) ∨
      ((Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom0683 chi) ∨
      (Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom0697 chi))) ∨
      (((Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom0797 chi) ∨
      (Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom1588 chi)) ∨
      ((¬Fin15AnchoredAtom2589 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom1588 chi) ∨
      (Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom0682 chi)))))) ∨
      ((((((Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom0684 chi) ∨
      (Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom0698 chi)) ∨
      ((Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom0798 chi) ∨
      (¬Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom1589 chi))) ∨
      (((Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom0683 chi) ∨
      (Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom0684 chi)) ∨
      ((Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom0699 chi) ∨
      (Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom0799 chi)))) ∨
      ((((Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom1590 chi) ∨
      (¬Fin15AnchoredAtom2591 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom1590 chi)) ∨
      ((Fin15AnchoredAtom2592 chi ∧
      ¬Fin15AnchoredAtom0685 chi) ∨
      (Fin15AnchoredAtom2592 chi ∧
      ¬Fin15AnchoredAtom0800 chi))) ∨
      (((¬Fin15AnchoredAtom2592 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0686 chi ∧
      Fin15AnchoredAtom0690 chi ∧
      Fin15AnchoredAtom0800 chi ∧
      Fin15AnchoredAtom1591 chi) ∨
      (Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom0685 chi)) ∨
      ((Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom0687 chi) ∨
      (Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom0691 chi))))) ∨
      (((((Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom0801 chi) ∨
      (Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom1592 chi)) ∨
      ((¬Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom1592 chi) ∨
      (Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom0685 chi))) ∨
      (((Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom0688 chi) ∨
      (Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom0692 chi)) ∨
      ((Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom0802 chi) ∨
      (Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom1593 chi)))) ∨
      ((((¬Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom1593 chi) ∨
      (Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom0685 chi)) ∨
      ((Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom0689 chi) ∨
      (Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom0693 chi))) ∨
      (((Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom0803 chi) ∨
      (Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom1594 chi)) ∨
      ((¬Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom1594 chi) ∨
      (Fin15AnchoredAtom2596 chi ∧
      ¬Fin15AnchoredAtom0686 chi))))))) ∨
      ((((((Fin15AnchoredAtom2596 chi ∧
      ¬Fin15AnchoredAtom0687 chi) ∨
      ((Fin15AnchoredAtom2596 chi ∧
      ¬Fin15AnchoredAtom0694 chi) ∨
      (Fin15AnchoredAtom2596 chi ∧
      ¬Fin15AnchoredAtom0804 chi))) ∨
      (((Fin15AnchoredAtom2596 chi ∧
      ¬Fin15AnchoredAtom1595 chi) ∨
      (¬Fin15AnchoredAtom2596 chi ∧
      Fin15AnchoredAtom0686 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom1595 chi)) ∨
      ((Fin15AnchoredAtom2597 chi ∧
      ¬Fin15AnchoredAtom0686 chi) ∨
      (Fin15AnchoredAtom2597 chi ∧
      ¬Fin15AnchoredAtom0695 chi)))) ∨
      ((((Fin15AnchoredAtom2597 chi ∧
      ¬Fin15AnchoredAtom0805 chi) ∨
      (¬Fin15AnchoredAtom2597 chi ∧
      Fin15AnchoredAtom0686 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0695 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom1596 chi)) ∨
      ((Fin15AnchoredAtom2598 chi ∧
      ¬Fin15AnchoredAtom0686 chi) ∨
      (Fin15AnchoredAtom2598 chi ∧
      ¬Fin15AnchoredAtom0689 chi))) ∨
      (((Fin15AnchoredAtom2598 chi ∧
      ¬Fin15AnchoredAtom0696 chi) ∨
      (Fin15AnchoredAtom2598 chi ∧
      ¬Fin15AnchoredAtom0806 chi)) ∨
      ((¬Fin15AnchoredAtom2598 chi ∧
      Fin15AnchoredAtom0686 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0696 chi ∧
      Fin15AnchoredAtom0806 chi ∧
      Fin15AnchoredAtom1597 chi) ∨
      (Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom0687 chi))))) ∨
      (((((Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom0688 chi) ∨
      (Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom0697 chi)) ∨
      ((Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom0807 chi) ∨
      (Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom1598 chi))) ∨
      (((¬Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom1598 chi) ∨
      (Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom0687 chi)) ∨
      ((Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom0689 chi) ∨
      (Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom0698 chi)))) ∨
      ((((Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom0808 chi) ∨
      (Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom1599 chi)) ∨
      ((¬Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom1599 chi) ∨
      (Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom0688 chi))) ∨
      (((Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom0689 chi) ∨
      (Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom0699 chi)) ∨
      ((Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom0809 chi) ∨
      (Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom1600 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom1600 chi) ∨
      (Fin15AnchoredAtom2602 chi ∧
      ¬Fin15AnchoredAtom0690 chi)) ∨
      ((Fin15AnchoredAtom2602 chi ∧
      ¬Fin15AnchoredAtom0691 chi) ∨
      (Fin15AnchoredAtom2602 chi ∧
      ¬Fin15AnchoredAtom0694 chi))) ∨
      (((Fin15AnchoredAtom2602 chi ∧
      ¬Fin15AnchoredAtom0810 chi) ∨
      (Fin15AnchoredAtom2602 chi ∧
      ¬Fin15AnchoredAtom1601 chi)) ∨
      ((¬Fin15AnchoredAtom2602 chi ∧
      Fin15AnchoredAtom0690 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom1601 chi) ∨
      (Fin15AnchoredAtom2603 chi ∧
      ¬Fin15AnchoredAtom0690 chi)))) ∨
      ((((Fin15AnchoredAtom2603 chi ∧
      ¬Fin15AnchoredAtom0692 chi) ∨
      (Fin15AnchoredAtom2603 chi ∧
      ¬Fin15AnchoredAtom0695 chi)) ∨
      ((Fin15AnchoredAtom2603 chi ∧
      ¬Fin15AnchoredAtom0811 chi) ∨
      (Fin15AnchoredAtom2603 chi ∧
      ¬Fin15AnchoredAtom1602 chi))) ∨
      (((¬Fin15AnchoredAtom2603 chi ∧
      Fin15AnchoredAtom0690 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0695 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom1602 chi) ∨
      (Fin15AnchoredAtom2604 chi ∧
      ¬Fin15AnchoredAtom0690 chi)) ∨
      ((Fin15AnchoredAtom2604 chi ∧
      ¬Fin15AnchoredAtom0693 chi) ∨
      (Fin15AnchoredAtom2604 chi ∧
      ¬Fin15AnchoredAtom0812 chi))))) ∨
      (((((Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom0691 chi) ∨
      (Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom0692 chi)) ∨
      ((Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom0697 chi) ∨
      (Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom0813 chi))) ∨
      (((Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom1604 chi) ∨
      (¬Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1604 chi)) ∨
      ((Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom0691 chi) ∨
      (Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom0693 chi)))) ∨
      ((((Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom0698 chi) ∨
      (Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom0814 chi)) ∨
      ((Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom1605 chi) ∨
      (¬Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1605 chi))) ∨
      (((Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom0692 chi) ∨
      (Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom0693 chi)) ∨
      ((Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom0699 chi) ∨
      (Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom0815 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom1606 chi) ∨
      ((¬Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1606 chi) ∨
      (Fin15AnchoredAtom2608 chi ∧
      ¬Fin15AnchoredAtom0694 chi))) ∨
      (((Fin15AnchoredAtom2608 chi ∧
      ¬Fin15AnchoredAtom0695 chi) ∨
      (Fin15AnchoredAtom2608 chi ∧
      ¬Fin15AnchoredAtom0697 chi)) ∨
      ((Fin15AnchoredAtom2608 chi ∧
      ¬Fin15AnchoredAtom0816 chi) ∨
      (Fin15AnchoredAtom2608 chi ∧
      ¬Fin15AnchoredAtom1607 chi)))) ∨
      ((((¬Fin15AnchoredAtom2608 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom0695 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0816 chi ∧
      Fin15AnchoredAtom1607 chi) ∨
      (Fin15AnchoredAtom2609 chi ∧
      ¬Fin15AnchoredAtom0696 chi)) ∨
      ((Fin15AnchoredAtom2609 chi ∧
      ¬Fin15AnchoredAtom0817 chi) ∨
      (Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom0697 chi))) ∨
      (((Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom0698 chi) ∨
      (Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom0699 chi)) ∨
      ((Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom0819 chi) ∨
      (Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom1610 chi))))) ∨
      (((((¬Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1610 chi) ∨
      (Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom0700 chi)) ∨
      ((Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom0701 chi) ∨
      (Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom0708 chi))) ∨
      (((Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom0736 chi) ∨
      (¬Fin15AnchoredAtom2612 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom1611 chi)) ∨
      ((Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom0700 chi) ∨
      (Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom0702 chi)))) ∨
      ((((Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom0709 chi) ∨
      (Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom0737 chi)) ∨
      ((Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom1612 chi) ∨
      (¬Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom1612 chi))) ∨
      (((Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom0700 chi) ∨
      (Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom0703 chi)) ∨
      ((Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom0710 chi) ∨
      (Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom0738 chi)))))) ∨
      ((((((Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom1613 chi) ∨
      (¬Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom1613 chi)) ∨
      ((Fin15AnchoredAtom2615 chi ∧
      ¬Fin15AnchoredAtom0700 chi) ∨
      (Fin15AnchoredAtom2615 chi ∧
      ¬Fin15AnchoredAtom0704 chi))) ∨
      (((Fin15AnchoredAtom2615 chi ∧
      ¬Fin15AnchoredAtom0739 chi) ∨
      (Fin15AnchoredAtom2615 chi ∧
      ¬Fin15AnchoredAtom1614 chi)) ∨
      ((¬Fin15AnchoredAtom2615 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom0711 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom1614 chi) ∨
      (Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom0700 chi)))) ∨
      ((((Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom0705 chi) ∨
      (Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom0712 chi)) ∨
      ((Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom0740 chi) ∨
      (Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom1615 chi))) ∨
      (((¬Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom1615 chi) ∨
      (Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom0700 chi)) ∨
      ((Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom0706 chi) ∨
      (Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom0713 chi))))) ∨
      (((((Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom0741 chi) ∨
      (Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom1616 chi)) ∨
      ((¬Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom1616 chi) ∨
      (Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom0700 chi))) ∨
      (((Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom0707 chi) ∨
      (Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom0714 chi)) ∨
      ((Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom0742 chi) ∨
      (Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom1617 chi)))) ∨
      ((((¬Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom1617 chi) ∨
      (Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom0701 chi)) ∨
      ((Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom0702 chi) ∨
      (Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom0715 chi))) ∨
      (((Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom0743 chi) ∨
      (Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom1618 chi)) ∨
      ((¬Fin15AnchoredAtom2619 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom1618 chi) ∨
      (Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom0701 chi))))))) ∨
      ((((((Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom0703 chi) ∨
      ((Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom0744 chi) ∨
      (¬Fin15AnchoredAtom2620 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom1619 chi))) ∨
      (((Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom0701 chi) ∨
      (Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom0705 chi)) ∨
      ((Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom0718 chi) ∨
      (Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom0746 chi)))) ∨
      ((((¬Fin15AnchoredAtom2622 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom1621 chi) ∨
      (Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom0701 chi)) ∨
      ((Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom0706 chi) ∨
      (Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom0747 chi))) ∨
      (((Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom1622 chi) ∨
      (¬Fin15AnchoredAtom2623 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom1622 chi)) ∨
      ((Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom0701 chi) ∨
      (Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom0707 chi))))) ∨
      (((((Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom0720 chi) ∨
      (Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom0748 chi)) ∨
      ((Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom1623 chi) ∨
      (¬Fin15AnchoredAtom2624 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom1623 chi))) ∨
      (((Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom0702 chi) ∨
      (Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom0703 chi)) ∨
      ((Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom0721 chi) ∨
      (Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom0749 chi)))) ∨
      ((((Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom1624 chi) ∨
      (¬Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom1624 chi)) ∨
      ((Fin15AnchoredAtom2626 chi ∧
      ¬Fin15AnchoredAtom0702 chi) ∨
      (Fin15AnchoredAtom2626 chi ∧
      ¬Fin15AnchoredAtom0704 chi))) ∨
      (((Fin15AnchoredAtom2626 chi ∧
      ¬Fin15AnchoredAtom0722 chi) ∨
      (Fin15AnchoredAtom2626 chi ∧
      ¬Fin15AnchoredAtom0750 chi)) ∨
      ((Fin15AnchoredAtom2626 chi ∧
      ¬Fin15AnchoredAtom1625 chi) ∨
      (¬Fin15AnchoredAtom2626 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom0722 chi ∧
      Fin15AnchoredAtom0750 chi ∧
      Fin15AnchoredAtom1625 chi)))))) ∨
      ((((((Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom0702 chi) ∨
      (Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom0705 chi)) ∨
      ((Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom0723 chi) ∨
      (Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom0751 chi))) ∨
      (((Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom1626 chi) ∨
      (¬Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom1626 chi)) ∨
      ((Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom0702 chi) ∨
      (Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom0706 chi)))) ∨
      ((((Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom0724 chi) ∨
      (Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom0752 chi)) ∨
      ((Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom1627 chi) ∨
      (¬Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom1627 chi))) ∨
      (((Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom0702 chi) ∨
      (Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom0707 chi)) ∨
      ((Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom0725 chi) ∨
      (Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom0753 chi))))) ∨
      (((((Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom1628 chi) ∨
      (¬Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom1628 chi)) ∨
      ((Fin15AnchoredAtom2630 chi ∧
      ¬Fin15AnchoredAtom0703 chi) ∨
      (Fin15AnchoredAtom2630 chi ∧
      ¬Fin15AnchoredAtom0704 chi))) ∨
      (((Fin15AnchoredAtom2630 chi ∧
      ¬Fin15AnchoredAtom0726 chi) ∨
      (Fin15AnchoredAtom2630 chi ∧
      ¬Fin15AnchoredAtom0754 chi)) ∨
      ((Fin15AnchoredAtom2630 chi ∧
      ¬Fin15AnchoredAtom1629 chi) ∨
      (¬Fin15AnchoredAtom2630 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom1629 chi)))) ∨
      ((((Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom0703 chi) ∨
      (Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom0705 chi)) ∨
      ((Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom0727 chi) ∨
      (Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom0755 chi))) ∨
      (((Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom1630 chi) ∨
      (¬Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom1630 chi)) ∨
      ((Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom0703 chi) ∨
      (Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom0706 chi)))))))))) := by
  intro hbad
  rcases hbad with hbad | hbad
  ·
    rcases hbad with hbad | hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause19182 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19183 chi hbad
                ·
                  exact fin15Anchored_clause19184 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19185 chi hbad
                ·
                  exact fin15Anchored_clause19186 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19187 chi hbad
                ·
                  exact fin15Anchored_clause19188 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19189 chi hbad
                ·
                  exact fin15Anchored_clause19190 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19191 chi hbad
                ·
                  exact fin15Anchored_clause19192 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19193 chi hbad
                ·
                  exact fin15Anchored_clause19194 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19195 chi hbad
                ·
                  exact fin15Anchored_clause19196 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19197 chi hbad
                ·
                  exact fin15Anchored_clause19198 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19199 chi hbad
                ·
                  exact fin15Anchored_clause19200 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19201 chi hbad
                ·
                  exact fin15Anchored_clause19202 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19203 chi hbad
                ·
                  exact fin15Anchored_clause19204 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19205 chi hbad
                ·
                  exact fin15Anchored_clause19206 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19207 chi hbad
                ·
                  exact fin15Anchored_clause19208 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19209 chi hbad
                ·
                  exact fin15Anchored_clause19210 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19211 chi hbad
                ·
                  exact fin15Anchored_clause19212 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19213 chi hbad
                ·
                  exact fin15Anchored_clause19214 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19215 chi hbad
                ·
                  exact fin15Anchored_clause19216 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19217 chi hbad
                ·
                  exact fin15Anchored_clause19218 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19219 chi hbad
                ·
                  exact fin15Anchored_clause19220 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19221 chi hbad
                ·
                  exact fin15Anchored_clause19222 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19223 chi hbad
                ·
                  exact fin15Anchored_clause19224 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19225 chi hbad
                ·
                  exact fin15Anchored_clause19226 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19227 chi hbad
                ·
                  exact fin15Anchored_clause19228 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19229 chi hbad
                ·
                  exact fin15Anchored_clause19230 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19231 chi hbad
                ·
                  exact fin15Anchored_clause19232 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19233 chi hbad
                ·
                  exact fin15Anchored_clause19234 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19235 chi hbad
                ·
                  exact fin15Anchored_clause19236 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19237 chi hbad
                ·
                  exact fin15Anchored_clause19238 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19239 chi hbad
                ·
                  exact fin15Anchored_clause19240 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19241 chi hbad
                ·
                  exact fin15Anchored_clause19242 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19243 chi hbad
                ·
                  exact fin15Anchored_clause19244 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause19245 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19246 chi hbad
                ·
                  exact fin15Anchored_clause19247 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19248 chi hbad
                ·
                  exact fin15Anchored_clause19249 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19250 chi hbad
                ·
                  exact fin15Anchored_clause19251 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19252 chi hbad
                ·
                  exact fin15Anchored_clause19253 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19254 chi hbad
                ·
                  exact fin15Anchored_clause19255 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19256 chi hbad
                ·
                  exact fin15Anchored_clause19257 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19258 chi hbad
                ·
                  exact fin15Anchored_clause19259 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19260 chi hbad
                ·
                  exact fin15Anchored_clause19261 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19262 chi hbad
                ·
                  exact fin15Anchored_clause19263 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19264 chi hbad
                ·
                  exact fin15Anchored_clause19265 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19266 chi hbad
                ·
                  exact fin15Anchored_clause19267 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19268 chi hbad
                ·
                  exact fin15Anchored_clause19269 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19270 chi hbad
                ·
                  exact fin15Anchored_clause19271 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19272 chi hbad
                ·
                  exact fin15Anchored_clause19273 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19274 chi hbad
                ·
                  exact fin15Anchored_clause19275 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19276 chi hbad
                ·
                  exact fin15Anchored_clause19277 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19278 chi hbad
                ·
                  exact fin15Anchored_clause19279 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19280 chi hbad
                ·
                  exact fin15Anchored_clause19281 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19282 chi hbad
                ·
                  exact fin15Anchored_clause19283 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19284 chi hbad
                ·
                  exact fin15Anchored_clause19285 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19286 chi hbad
                ·
                  exact fin15Anchored_clause19287 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19288 chi hbad
                ·
                  exact fin15Anchored_clause19289 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19290 chi hbad
                ·
                  exact fin15Anchored_clause19291 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19292 chi hbad
                ·
                  exact fin15Anchored_clause19293 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19294 chi hbad
                ·
                  exact fin15Anchored_clause19295 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19296 chi hbad
                ·
                  exact fin15Anchored_clause19297 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19298 chi hbad
                ·
                  exact fin15Anchored_clause19299 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19300 chi hbad
                ·
                  exact fin15Anchored_clause19301 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19302 chi hbad
                ·
                  exact fin15Anchored_clause19303 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19304 chi hbad
                ·
                  exact fin15Anchored_clause19305 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19306 chi hbad
                ·
                  exact fin15Anchored_clause19307 chi hbad
  ·
    rcases hbad with hbad | hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause19308 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19309 chi hbad
                ·
                  exact fin15Anchored_clause19310 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19311 chi hbad
                ·
                  exact fin15Anchored_clause19312 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19313 chi hbad
                ·
                  exact fin15Anchored_clause19314 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19315 chi hbad
                ·
                  exact fin15Anchored_clause19316 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19317 chi hbad
                ·
                  exact fin15Anchored_clause19318 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19319 chi hbad
                ·
                  exact fin15Anchored_clause19320 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19321 chi hbad
                ·
                  exact fin15Anchored_clause19322 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19323 chi hbad
                ·
                  exact fin15Anchored_clause19324 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19325 chi hbad
                ·
                  exact fin15Anchored_clause19326 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19327 chi hbad
                ·
                  exact fin15Anchored_clause19328 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19329 chi hbad
                ·
                  exact fin15Anchored_clause19330 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19331 chi hbad
                ·
                  exact fin15Anchored_clause19332 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19333 chi hbad
                ·
                  exact fin15Anchored_clause19334 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19335 chi hbad
                ·
                  exact fin15Anchored_clause19336 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19337 chi hbad
                ·
                  exact fin15Anchored_clause19338 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19339 chi hbad
                ·
                  exact fin15Anchored_clause19340 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19341 chi hbad
                ·
                  exact fin15Anchored_clause19342 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19343 chi hbad
                ·
                  exact fin15Anchored_clause19344 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19345 chi hbad
                ·
                  exact fin15Anchored_clause19346 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19347 chi hbad
                ·
                  exact fin15Anchored_clause19348 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19349 chi hbad
                ·
                  exact fin15Anchored_clause19350 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19351 chi hbad
                ·
                  exact fin15Anchored_clause19352 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19353 chi hbad
                ·
                  exact fin15Anchored_clause19354 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19355 chi hbad
                ·
                  exact fin15Anchored_clause19356 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19357 chi hbad
                ·
                  exact fin15Anchored_clause19358 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19359 chi hbad
                ·
                  exact fin15Anchored_clause19360 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19361 chi hbad
                ·
                  exact fin15Anchored_clause19362 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19363 chi hbad
                ·
                  exact fin15Anchored_clause19364 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19365 chi hbad
                ·
                  exact fin15Anchored_clause19366 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19367 chi hbad
                ·
                  exact fin15Anchored_clause19368 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19369 chi hbad
                ·
                  exact fin15Anchored_clause19370 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause19371 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19372 chi hbad
                ·
                  exact fin15Anchored_clause19373 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19374 chi hbad
                ·
                  exact fin15Anchored_clause19375 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19376 chi hbad
                ·
                  exact fin15Anchored_clause19377 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19378 chi hbad
                ·
                  exact fin15Anchored_clause19379 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19380 chi hbad
                ·
                  exact fin15Anchored_clause19381 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19382 chi hbad
                ·
                  exact fin15Anchored_clause19383 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19384 chi hbad
                ·
                  exact fin15Anchored_clause19385 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19386 chi hbad
                ·
                  exact fin15Anchored_clause19387 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19388 chi hbad
                ·
                  exact fin15Anchored_clause19389 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19390 chi hbad
                ·
                  exact fin15Anchored_clause19391 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19392 chi hbad
                ·
                  exact fin15Anchored_clause19393 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19394 chi hbad
                ·
                  exact fin15Anchored_clause19395 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19396 chi hbad
                ·
                  exact fin15Anchored_clause19397 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19398 chi hbad
                ·
                  exact fin15Anchored_clause19399 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19400 chi hbad
                ·
                  exact fin15Anchored_clause19401 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19402 chi hbad
                ·
                  exact fin15Anchored_clause19403 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19404 chi hbad
                ·
                  exact fin15Anchored_clause19405 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19406 chi hbad
                ·
                  exact fin15Anchored_clause19407 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19408 chi hbad
                ·
                  exact fin15Anchored_clause19409 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19410 chi hbad
                ·
                  exact fin15Anchored_clause19411 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19412 chi hbad
                ·
                  exact fin15Anchored_clause19413 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19414 chi hbad
                ·
                  exact fin15Anchored_clause19415 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19416 chi hbad
                ·
                  exact fin15Anchored_clause19417 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19418 chi hbad
                ·
                  exact fin15Anchored_clause19419 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19420 chi hbad
                ·
                  exact fin15Anchored_clause19421 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19422 chi hbad
                ·
                  exact fin15Anchored_clause19423 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19424 chi hbad
                ·
                  exact fin15Anchored_clause19425 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19426 chi hbad
                ·
                  exact fin15Anchored_clause19427 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19428 chi hbad
                ·
                  exact fin15Anchored_clause19429 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19430 chi hbad
                ·
                  exact fin15Anchored_clause19431 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause19432 chi hbad
                ·
                  exact fin15Anchored_clause19433 chi hbad

end ErdosSzekeres

end
