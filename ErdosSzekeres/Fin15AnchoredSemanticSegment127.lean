module

public import ErdosSzekeres.Fin15AnchoredClauseChunk250
public import ErdosSzekeres.Fin15AnchoredClauseChunk251
public import ErdosSzekeres.Fin15AnchoredClauseChunk252

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 127. -/

theorem fin15Anchored_rejectSemanticSegment127
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4716 chi) ∨
      ((¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4720 chi) ∨
      (¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4721 chi))) ∨
      (((¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4722 chi) ∨
      (¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4726 chi)) ∨
      ((¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4727 chi) ∨
      (¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4728 chi)))) ∨
      ((((¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4732 chi) ∨
      (¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4756 chi)) ∨
      ((¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4757 chi) ∨
      (¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4758 chi))) ∨
      (((¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4762 chi) ∨
      (¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4766 chi)) ∨
      ((¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4791 chi) ∨
      (¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4792 chi))))) ∨
      (((((¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4793 chi) ∨
      (¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4797 chi)) ∨
      ((¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4801 chi) ∨
      (¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4821 chi))) ∨
      (((¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4791 chi) ∨
      (¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4792 chi)) ∨
      ((¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4793 chi) ∨
      (¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4797 chi)))) ∨
      ((((¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4801 chi) ∨
      (¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4821 chi)) ∨
      ((¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4821 chi) ∨
      (¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3706 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3713 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3724 chi ∧
      ¬Fin15AnchoredAtom3728 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3741 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3752 chi ∧
      ¬Fin15AnchoredAtom3756 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3773 chi ∧
      ¬Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom3802 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3825 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3836 chi ∧
      ¬Fin15AnchoredAtom3840 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3857 chi ∧
      ¬Fin15AnchoredAtom3861 chi ∧
      ¬Fin15AnchoredAtom3886 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3913 chi ∧
      ¬Fin15AnchoredAtom3917 chi ∧
      ¬Fin15AnchoredAtom3942 chi ∧
      ¬Fin15AnchoredAtom3977 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4365 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4376 chi ∧
      ¬Fin15AnchoredAtom4380 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4397 chi ∧
      ¬Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom4426 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4453 chi ∧
      ¬Fin15AnchoredAtom4457 chi ∧
      ¬Fin15AnchoredAtom4482 chi ∧
      ¬Fin15AnchoredAtom4517 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4579 chi ∧
      ¬Fin15AnchoredAtom4583 chi ∧
      ¬Fin15AnchoredAtom4608 chi ∧
      ¬Fin15AnchoredAtom4643 chi ∧
      ¬Fin15AnchoredAtom4713 chi))) ∨
      (((¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4714 chi) ∨
      (¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4715 chi)) ∨
      ((¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4716 chi) ∨
      (¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4720 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4721 chi) ∨
      (¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4722 chi)) ∨
      ((¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3706 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3713 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3728 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3732 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3741 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3756 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3760 chi ∧
      ¬Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3781 chi ∧
      ¬Fin15AnchoredAtom3812 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3825 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3840 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3844 chi ∧
      ¬Fin15AnchoredAtom3861 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3865 chi ∧
      ¬Fin15AnchoredAtom3896 chi ∧
      ¬Fin15AnchoredAtom3917 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3921 chi ∧
      ¬Fin15AnchoredAtom3952 chi ∧
      ¬Fin15AnchoredAtom3987 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4365 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4380 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4384 chi ∧
      ¬Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4405 chi ∧
      ¬Fin15AnchoredAtom4436 chi ∧
      ¬Fin15AnchoredAtom4457 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4461 chi ∧
      ¬Fin15AnchoredAtom4492 chi ∧
      ¬Fin15AnchoredAtom4527 chi ∧
      ¬Fin15AnchoredAtom4583 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4587 chi ∧
      ¬Fin15AnchoredAtom4618 chi ∧
      ¬Fin15AnchoredAtom4653 chi ∧
      ¬Fin15AnchoredAtom4723 chi) ∨
      (¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4726 chi))) ∨
      (((¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4727 chi) ∨
      (¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4728 chi)) ∨
      ((¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4732 chi) ∨
      (¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4756 chi)))) ∨
      ((((¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4757 chi) ∨
      (¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4758 chi)) ∨
      ((¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4762 chi) ∨
      (¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4766 chi))) ∨
      (((¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3713 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3724 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3728 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3733 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3773 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3782 chi ∧
      ¬Fin15AnchoredAtom3802 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3807 chi ∧
      ¬Fin15AnchoredAtom3813 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3857 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3861 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3866 chi ∧
      ¬Fin15AnchoredAtom3886 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3891 chi ∧
      ¬Fin15AnchoredAtom3897 chi ∧
      ¬Fin15AnchoredAtom3977 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3982 chi ∧
      ¬Fin15AnchoredAtom3988 chi ∧
      ¬Fin15AnchoredAtom4018 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4397 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4406 chi ∧
      ¬Fin15AnchoredAtom4426 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4431 chi ∧
      ¬Fin15AnchoredAtom4437 chi ∧
      ¬Fin15AnchoredAtom4517 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4522 chi ∧
      ¬Fin15AnchoredAtom4528 chi ∧
      ¬Fin15AnchoredAtom4558 chi ∧
      ¬Fin15AnchoredAtom4643 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4648 chi ∧
      ¬Fin15AnchoredAtom4654 chi ∧
      ¬Fin15AnchoredAtom4684 chi ∧
      ¬Fin15AnchoredAtom4789 chi) ∨
      (¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4791 chi)) ∨
      ((¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4792 chi) ∨
      (¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4793 chi))))) ∨
      (((((¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3713 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3724 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3732 chi ∧
      ¬Fin15AnchoredAtom3733 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3773 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3781 chi ∧
      ¬Fin15AnchoredAtom3782 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3806 chi ∧
      ¬Fin15AnchoredAtom3807 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3818 chi ∧
      ¬Fin15AnchoredAtom3857 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3865 chi ∧
      ¬Fin15AnchoredAtom3866 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3890 chi ∧
      ¬Fin15AnchoredAtom3891 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3902 chi ∧
      ¬Fin15AnchoredAtom3981 chi ∧
      ¬Fin15AnchoredAtom3982 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3993 chi ∧
      ¬Fin15AnchoredAtom4023 chi ∧
      ¬Fin15AnchoredAtom4397 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4405 chi ∧
      ¬Fin15AnchoredAtom4406 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4430 chi ∧
      ¬Fin15AnchoredAtom4431 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4442 chi ∧
      ¬Fin15AnchoredAtom4521 chi ∧
      ¬Fin15AnchoredAtom4522 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4533 chi ∧
      ¬Fin15AnchoredAtom4563 chi ∧
      ¬Fin15AnchoredAtom4647 chi ∧
      ¬Fin15AnchoredAtom4648 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom4689 chi ∧
      ¬Fin15AnchoredAtom4794 chi) ∨
      (¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4797 chi)) ∨
      ((¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4801 chi) ∨
      (¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4821 chi))) ∨
      (((¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3741 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3752 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3756 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3762 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3773 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3783 chi ∧
      ¬Fin15AnchoredAtom3802 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3808 chi ∧
      ¬Fin15AnchoredAtom3814 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3913 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3917 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3923 chi ∧
      ¬Fin15AnchoredAtom3942 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3948 chi ∧
      ¬Fin15AnchoredAtom3954 chi ∧
      ¬Fin15AnchoredAtom3977 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3983 chi ∧
      ¬Fin15AnchoredAtom3989 chi ∧
      ¬Fin15AnchoredAtom4019 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4453 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4457 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4463 chi ∧
      ¬Fin15AnchoredAtom4482 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4488 chi ∧
      ¬Fin15AnchoredAtom4494 chi ∧
      ¬Fin15AnchoredAtom4517 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4523 chi ∧
      ¬Fin15AnchoredAtom4529 chi ∧
      ¬Fin15AnchoredAtom4559 chi ∧
      ¬Fin15AnchoredAtom4713 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4719 chi ∧
      ¬Fin15AnchoredAtom4725 chi ∧
      ¬Fin15AnchoredAtom4755 chi ∧
      ¬Fin15AnchoredAtom4790 chi) ∨
      (¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4791 chi)) ∨
      ((¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4792 chi) ∨
      (¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4793 chi)))) ∨
      ((((¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4797 chi) ∨
      (¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4801 chi)) ∨
      ((¬Fin15AnchoredAtom3746 chi ∧
      ¬Fin15AnchoredAtom3748 chi ∧
      ¬Fin15AnchoredAtom3749 chi ∧
      ¬Fin15AnchoredAtom3750 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3793 chi ∧
      ¬Fin15AnchoredAtom3794 chi ∧
      ¬Fin15AnchoredAtom3795 chi ∧
      ¬Fin15AnchoredAtom3799 chi ∧
      ¬Fin15AnchoredAtom3800 chi ∧
      ¬Fin15AnchoredAtom3801 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3933 chi ∧
      ¬Fin15AnchoredAtom3934 chi ∧
      ¬Fin15AnchoredAtom3935 chi ∧
      ¬Fin15AnchoredAtom3939 chi ∧
      ¬Fin15AnchoredAtom3940 chi ∧
      ¬Fin15AnchoredAtom3941 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4010 chi ∧
      ¬Fin15AnchoredAtom4011 chi ∧
      ¬Fin15AnchoredAtom4012 chi ∧
      ¬Fin15AnchoredAtom4016 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4816 chi) ∨
      (¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4821 chi))) ∨
      (((¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4821 chi) ∨
      (¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4791 chi)) ∨
      ((¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4792 chi) ∨
      (¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4793 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3825 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3836 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3844 chi ∧
      ¬Fin15AnchoredAtom3845 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3857 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3865 chi ∧
      ¬Fin15AnchoredAtom3866 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3890 chi ∧
      ¬Fin15AnchoredAtom3891 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3902 chi ∧
      ¬Fin15AnchoredAtom3913 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3921 chi ∧
      ¬Fin15AnchoredAtom3922 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3946 chi ∧
      ¬Fin15AnchoredAtom3947 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3958 chi ∧
      ¬Fin15AnchoredAtom3981 chi ∧
      ¬Fin15AnchoredAtom3982 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3993 chi ∧
      ¬Fin15AnchoredAtom4023 chi ∧
      ¬Fin15AnchoredAtom4579 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4587 chi ∧
      ¬Fin15AnchoredAtom4588 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4612 chi ∧
      ¬Fin15AnchoredAtom4613 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4624 chi ∧
      ¬Fin15AnchoredAtom4647 chi ∧
      ¬Fin15AnchoredAtom4648 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom4689 chi ∧
      ¬Fin15AnchoredAtom4717 chi ∧
      ¬Fin15AnchoredAtom4718 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4729 chi ∧
      ¬Fin15AnchoredAtom4759 chi ∧
      ¬Fin15AnchoredAtom4794 chi) ∨
      ((¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4797 chi) ∨
      (¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4801 chi))) ∨
      (((¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4821 chi) ∨
      (¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom3900 chi ∧
      ¬Fin15AnchoredAtom3901 chi ∧
      ¬Fin15AnchoredAtom3905 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4821 chi)) ∨
      ((¬Fin15AnchoredAtom3912 chi ∧
      ¬Fin15AnchoredAtom3914 chi ∧
      ¬Fin15AnchoredAtom3915 chi ∧
      ¬Fin15AnchoredAtom3916 chi ∧
      ¬Fin15AnchoredAtom3918 chi ∧
      ¬Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom3961 chi ∧
      ¬Fin15AnchoredAtom3978 chi ∧
      ¬Fin15AnchoredAtom3979 chi ∧
      ¬Fin15AnchoredAtom3980 chi ∧
      ¬Fin15AnchoredAtom3984 chi ∧
      ¬Fin15AnchoredAtom3985 chi ∧
      ¬Fin15AnchoredAtom3986 chi ∧
      ¬Fin15AnchoredAtom3990 chi ∧
      ¬Fin15AnchoredAtom3991 chi ∧
      ¬Fin15AnchoredAtom3992 chi ∧
      ¬Fin15AnchoredAtom3996 chi ∧
      ¬Fin15AnchoredAtom4020 chi ∧
      ¬Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4821 chi) ∨
      (¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4698 chi)))) ∨
      ((((¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4700 chi) ∨
      (¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4702 chi)) ∨
      ((¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4704 chi) ∨
      (¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4705 chi))) ∨
      (((¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4125 chi ∧
      ¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4706 chi) ∨
      (¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom4710 chi)) ∨
      ((¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4130 chi ∧
      ¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4424 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom4711 chi) ∨
      (¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4714 chi))))) ∨
      (((((¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4715 chi) ∨
      (¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4716 chi)) ∨
      ((¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4720 chi) ∨
      (¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4721 chi))) ∨
      (((¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4722 chi) ∨
      (¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4726 chi)) ∨
      ((¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4727 chi) ∨
      (¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4728 chi)))) ∨
      ((((¬Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4732 chi) ∨
      (¬Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4735 chi)) ∨
      ((¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4756 chi) ∨
      (¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4757 chi))) ∨
      (((¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4758 chi) ∨
      (¬Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4762 chi)) ∨
      ((¬Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4766 chi) ∨
      (¬Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4775 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4791 chi) ∨
      (¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4792 chi)) ∨
      ((¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4793 chi) ∨
      (¬Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4797 chi))) ∨
      (((¬Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4801 chi) ∨
      (¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4806 chi)) ∨
      ((¬Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom4125 chi ∧
      ¬Fin15AnchoredAtom4130 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom4424 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4807 chi) ∨
      (¬Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4821 chi)))) ∨
      ((((¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4769 chi) ∨
      (¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4770 chi)) ∨
      ((¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom4125 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4771 chi) ∨
      (¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom4130 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4776 chi))) ∨
      (((¬Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom4080 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom4131 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom4777 chi) ∨
      (¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4791 chi)) ∨
      ((¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4792 chi) ∨
      (¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4793 chi))))) ∨
      (((((¬Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4797 chi) ∨
      (¬Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4801 chi)) ∨
      ((¬Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom4076 chi ∧
      ¬Fin15AnchoredAtom4078 chi ∧
      ¬Fin15AnchoredAtom4079 chi ∧
      ¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4806 chi) ∨
      (¬Fin15AnchoredAtom4081 chi ∧
      ¬Fin15AnchoredAtom4083 chi ∧
      ¬Fin15AnchoredAtom4084 chi ∧
      ¬Fin15AnchoredAtom4085 chi ∧
      ¬Fin15AnchoredAtom4087 chi ∧
      ¬Fin15AnchoredAtom4088 chi ∧
      ¬Fin15AnchoredAtom4089 chi ∧
      ¬Fin15AnchoredAtom4093 chi ∧
      ¬Fin15AnchoredAtom4094 chi ∧
      ¬Fin15AnchoredAtom4095 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4821 chi))) ∨
      (((¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4097 chi ∧
      ¬Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4806 chi) ∨
      (¬Fin15AnchoredAtom4096 chi ∧
      ¬Fin15AnchoredAtom4099 chi ∧
      ¬Fin15AnchoredAtom4100 chi ∧
      ¬Fin15AnchoredAtom4101 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom4130 chi ∧
      ¬Fin15AnchoredAtom4131 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom4346 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4812 chi)) ∨
      ((¬Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4821 chi) ∨
      (¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4771 chi)))) ∨
      ((((¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom4775 chi) ∨
      (¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4776 chi)) ∨
      ((¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom4777 chi) ∨
      (¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4781 chi))) ∨
      (((¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom4783 chi) ∨
      (¬Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4346 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom4787 chi)) ∨
      ((¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4791 chi) ∨
      (¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4792 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4793 chi) ∨
      ((¬Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4797 chi) ∨
      (¬Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4801 chi))) ∨
      (((¬Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4807 chi) ∨
      (¬Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4808 chi)) ∨
      ((¬Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom4346 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4816 chi) ∨
      (¬Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4821 chi)))) ∨
      ((((¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4806 chi) ∨
      (¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4807 chi)) ∨
      ((¬Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4808 chi) ∨
      (¬Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom4346 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4816 chi))) ∨
      (((¬Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4821 chi) ∨
      (¬Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom4219 chi ∧
      ¬Fin15AnchoredAtom4223 chi ∧
      ¬Fin15AnchoredAtom4224 chi ∧
      ¬Fin15AnchoredAtom4225 chi ∧
      ¬Fin15AnchoredAtom4229 chi ∧
      ¬Fin15AnchoredAtom4230 chi ∧
      ¬Fin15AnchoredAtom4231 chi ∧
      ¬Fin15AnchoredAtom4235 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom4346 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom4807 chi ∧
      ¬Fin15AnchoredAtom4808 chi ∧
      ¬Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom4821 chi)) ∨
      ((¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4237 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4808 chi) ∨
      (¬Fin15AnchoredAtom4236 chi ∧
      ¬Fin15AnchoredAtom4239 chi ∧
      ¬Fin15AnchoredAtom4240 chi ∧
      ¬Fin15AnchoredAtom4241 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom4346 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4812 chi))))) ∨
      (((((¬Fin15AnchoredAtom4242 chi ∧
      ¬Fin15AnchoredAtom4244 chi ∧
      ¬Fin15AnchoredAtom4245 chi ∧
      ¬Fin15AnchoredAtom4246 chi ∧
      ¬Fin15AnchoredAtom4248 chi ∧
      ¬Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4821 chi) ∨
      (¬Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom4320 chi ∧
      ¬Fin15AnchoredAtom4321 chi ∧
      ¬Fin15AnchoredAtom4322 chi ∧
      ¬Fin15AnchoredAtom4326 chi ∧
      ¬Fin15AnchoredAtom4328 chi ∧
      ¬Fin15AnchoredAtom4329 chi ∧
      ¬Fin15AnchoredAtom4330 chi ∧
      ¬Fin15AnchoredAtom4334 chi ∧
      ¬Fin15AnchoredAtom4335 chi ∧
      ¬Fin15AnchoredAtom4336 chi ∧
      ¬Fin15AnchoredAtom4340 chi ∧
      ¬Fin15AnchoredAtom4341 chi ∧
      ¬Fin15AnchoredAtom4342 chi ∧
      ¬Fin15AnchoredAtom4346 chi ∧
      ¬Fin15AnchoredAtom4350 chi ∧
      ¬Fin15AnchoredAtom4351 chi ∧
      ¬Fin15AnchoredAtom4352 chi ∧
      ¬Fin15AnchoredAtom4356 chi ∧
      ¬Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom4807 chi ∧
      ¬Fin15AnchoredAtom4808 chi ∧
      ¬Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom4821 chi)) ∨
      ((¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4781 chi) ∨
      (¬Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4576 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom4783 chi))) ∨
      (((¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4365 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4376 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4380 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4385 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4397 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4406 chi ∧
      ¬Fin15AnchoredAtom4426 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4431 chi ∧
      ¬Fin15AnchoredAtom4437 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4453 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4457 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4462 chi ∧
      ¬Fin15AnchoredAtom4482 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4487 chi ∧
      ¬Fin15AnchoredAtom4493 chi ∧
      ¬Fin15AnchoredAtom4517 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4522 chi ∧
      ¬Fin15AnchoredAtom4528 chi ∧
      ¬Fin15AnchoredAtom4558 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4579 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4583 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4588 chi ∧
      ¬Fin15AnchoredAtom4608 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4613 chi ∧
      ¬Fin15AnchoredAtom4619 chi ∧
      ¬Fin15AnchoredAtom4643 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4648 chi ∧
      ¬Fin15AnchoredAtom4654 chi ∧
      ¬Fin15AnchoredAtom4684 chi ∧
      ¬Fin15AnchoredAtom4713 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4718 chi ∧
      ¬Fin15AnchoredAtom4724 chi ∧
      ¬Fin15AnchoredAtom4754 chi ∧
      ¬Fin15AnchoredAtom4789 chi) ∨
      (¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4791 chi)) ∨
      ((¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4792 chi) ∨
      (¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4793 chi)))) ∨
      ((((¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4365 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4376 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4384 chi ∧
      ¬Fin15AnchoredAtom4385 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4397 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4405 chi ∧
      ¬Fin15AnchoredAtom4406 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4430 chi ∧
      ¬Fin15AnchoredAtom4431 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4442 chi ∧
      ¬Fin15AnchoredAtom4453 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4461 chi ∧
      ¬Fin15AnchoredAtom4462 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4486 chi ∧
      ¬Fin15AnchoredAtom4487 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4498 chi ∧
      ¬Fin15AnchoredAtom4521 chi ∧
      ¬Fin15AnchoredAtom4522 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4533 chi ∧
      ¬Fin15AnchoredAtom4563 chi ∧
      ¬Fin15AnchoredAtom4579 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4587 chi ∧
      ¬Fin15AnchoredAtom4588 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4612 chi ∧
      ¬Fin15AnchoredAtom4613 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4624 chi ∧
      ¬Fin15AnchoredAtom4647 chi ∧
      ¬Fin15AnchoredAtom4648 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom4689 chi ∧
      ¬Fin15AnchoredAtom4717 chi ∧
      ¬Fin15AnchoredAtom4718 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4729 chi ∧
      ¬Fin15AnchoredAtom4759 chi ∧
      ¬Fin15AnchoredAtom4794 chi) ∨
      (¬Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4797 chi)) ∨
      ((¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4365 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4380 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4384 chi ∧
      ¬Fin15AnchoredAtom4385 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4405 chi ∧
      ¬Fin15AnchoredAtom4406 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4436 chi ∧
      ¬Fin15AnchoredAtom4437 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4442 chi ∧
      ¬Fin15AnchoredAtom4457 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4461 chi ∧
      ¬Fin15AnchoredAtom4462 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4492 chi ∧
      ¬Fin15AnchoredAtom4493 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4498 chi ∧
      ¬Fin15AnchoredAtom4527 chi ∧
      ¬Fin15AnchoredAtom4528 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4533 chi ∧
      ¬Fin15AnchoredAtom4567 chi ∧
      ¬Fin15AnchoredAtom4583 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4587 chi ∧
      ¬Fin15AnchoredAtom4588 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4618 chi ∧
      ¬Fin15AnchoredAtom4619 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4624 chi ∧
      ¬Fin15AnchoredAtom4653 chi ∧
      ¬Fin15AnchoredAtom4654 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom4693 chi ∧
      ¬Fin15AnchoredAtom4723 chi ∧
      ¬Fin15AnchoredAtom4724 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4729 chi ∧
      ¬Fin15AnchoredAtom4763 chi ∧
      ¬Fin15AnchoredAtom4798 chi) ∨
      (¬Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4801 chi))) ∨
      (((¬Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom4424 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4807 chi) ∨
      (¬Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4821 chi)) ∨
      ((¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4397 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4405 chi ∧
      ¬Fin15AnchoredAtom4406 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4426 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4430 chi ∧
      ¬Fin15AnchoredAtom4431 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4436 chi ∧
      ¬Fin15AnchoredAtom4437 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4442 chi ∧
      ¬Fin15AnchoredAtom4517 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4521 chi ∧
      ¬Fin15AnchoredAtom4522 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4527 chi ∧
      ¬Fin15AnchoredAtom4528 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4533 chi ∧
      ¬Fin15AnchoredAtom4557 chi ∧
      ¬Fin15AnchoredAtom4558 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4563 chi ∧
      ¬Fin15AnchoredAtom4567 chi ∧
      ¬Fin15AnchoredAtom4643 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4647 chi ∧
      ¬Fin15AnchoredAtom4648 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4653 chi ∧
      ¬Fin15AnchoredAtom4654 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom4683 chi ∧
      ¬Fin15AnchoredAtom4684 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4689 chi ∧
      ¬Fin15AnchoredAtom4693 chi ∧
      ¬Fin15AnchoredAtom4788 chi ∧
      ¬Fin15AnchoredAtom4789 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4794 chi ∧
      ¬Fin15AnchoredAtom4798 chi ∧
      ¬Fin15AnchoredAtom4818 chi) ∨
      (¬Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4821 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4821 chi) ∨
      (¬Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom4530 chi ∧
      ¬Fin15AnchoredAtom4531 chi ∧
      ¬Fin15AnchoredAtom4532 chi ∧
      ¬Fin15AnchoredAtom4536 chi ∧
      ¬Fin15AnchoredAtom4538 chi ∧
      ¬Fin15AnchoredAtom4539 chi ∧
      ¬Fin15AnchoredAtom4540 chi ∧
      ¬Fin15AnchoredAtom4544 chi ∧
      ¬Fin15AnchoredAtom4545 chi ∧
      ¬Fin15AnchoredAtom4546 chi ∧
      ¬Fin15AnchoredAtom4550 chi ∧
      ¬Fin15AnchoredAtom4551 chi ∧
      ¬Fin15AnchoredAtom4552 chi ∧
      ¬Fin15AnchoredAtom4556 chi ∧
      ¬Fin15AnchoredAtom4560 chi ∧
      ¬Fin15AnchoredAtom4561 chi ∧
      ¬Fin15AnchoredAtom4562 chi ∧
      ¬Fin15AnchoredAtom4566 chi ∧
      ¬Fin15AnchoredAtom4570 chi ∧
      ¬Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom4807 chi ∧
      ¬Fin15AnchoredAtom4808 chi ∧
      ¬Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom4821 chi)) ∨
      ((¬Fin15AnchoredAtom4572 chi ∧
      ¬Fin15AnchoredAtom4573 chi ∧
      ¬Fin15AnchoredAtom4575 chi ∧
      ¬Fin15AnchoredAtom4577 chi ∧
      ¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4807 chi) ∨
      (¬Fin15AnchoredAtom4578 chi ∧
      ¬Fin15AnchoredAtom4580 chi ∧
      ¬Fin15AnchoredAtom4581 chi ∧
      ¬Fin15AnchoredAtom4582 chi ∧
      ¬Fin15AnchoredAtom4584 chi ∧
      ¬Fin15AnchoredAtom4585 chi ∧
      ¬Fin15AnchoredAtom4586 chi ∧
      ¬Fin15AnchoredAtom4590 chi ∧
      ¬Fin15AnchoredAtom4591 chi ∧
      ¬Fin15AnchoredAtom4592 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4821 chi))) ∨
      (((¬Fin15AnchoredAtom4593 chi ∧
      ¬Fin15AnchoredAtom4595 chi ∧
      ¬Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom4807 chi ∧
      ¬Fin15AnchoredAtom4808 chi ∧
      ¬Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom4821 chi) ∨
      (¬Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom4801 chi ∧
      ¬Fin15AnchoredAtom4806 chi ∧
      ¬Fin15AnchoredAtom4807 chi ∧
      ¬Fin15AnchoredAtom4808 chi ∧
      ¬Fin15AnchoredAtom4812 chi ∧
      ¬Fin15AnchoredAtom4816 chi ∧
      ¬Fin15AnchoredAtom4821 chi)) ∨
      ((Fin15AnchoredAtom0001 chi) ∨
      (Fin15AnchoredAtom0002 chi)))) ∨
      ((((Fin15AnchoredAtom0003 chi) ∨
      (Fin15AnchoredAtom0004 chi)) ∨
      ((Fin15AnchoredAtom0005 chi) ∨
      (Fin15AnchoredAtom0006 chi))) ∨
      (((Fin15AnchoredAtom0007 chi) ∨
      (Fin15AnchoredAtom0008 chi)) ∨
      ((Fin15AnchoredAtom0009 chi) ∨
      (Fin15AnchoredAtom0010 chi))))) ∨
      (((((Fin15AnchoredAtom0011 chi) ∨
      (Fin15AnchoredAtom0012 chi)) ∨
      ((Fin15AnchoredAtom0013 chi) ∨
      (Fin15AnchoredAtom0014 chi))) ∨
      (((Fin15AnchoredAtom0015 chi) ∨
      (Fin15AnchoredAtom0016 chi)) ∨
      ((Fin15AnchoredAtom0017 chi) ∨
      (Fin15AnchoredAtom0018 chi)))) ∨
      ((((Fin15AnchoredAtom0019 chi) ∨
      (Fin15AnchoredAtom0020 chi)) ∨
      ((Fin15AnchoredAtom0021 chi) ∨
      (Fin15AnchoredAtom0022 chi))) ∨
      (((Fin15AnchoredAtom0023 chi) ∨
      (Fin15AnchoredAtom0024 chi)) ∨
      ((Fin15AnchoredAtom0025 chi) ∨
      (Fin15AnchoredAtom0026 chi))))))) ∨
      (((((((Fin15AnchoredAtom0027 chi) ∨
      (Fin15AnchoredAtom0028 chi)) ∨
      ((Fin15AnchoredAtom0029 chi) ∨
      (Fin15AnchoredAtom0030 chi))) ∨
      (((Fin15AnchoredAtom0031 chi) ∨
      (Fin15AnchoredAtom0032 chi)) ∨
      ((Fin15AnchoredAtom0033 chi) ∨
      (Fin15AnchoredAtom0034 chi)))) ∨
      ((((Fin15AnchoredAtom0035 chi) ∨
      (Fin15AnchoredAtom0036 chi)) ∨
      ((Fin15AnchoredAtom0037 chi) ∨
      (Fin15AnchoredAtom0038 chi))) ∨
      (((Fin15AnchoredAtom0039 chi) ∨
      (Fin15AnchoredAtom0040 chi)) ∨
      ((Fin15AnchoredAtom0041 chi) ∨
      (Fin15AnchoredAtom0042 chi))))) ∨
      (((((Fin15AnchoredAtom0043 chi) ∨
      (Fin15AnchoredAtom0044 chi)) ∨
      ((Fin15AnchoredAtom0045 chi) ∨
      (Fin15AnchoredAtom0046 chi))) ∨
      (((Fin15AnchoredAtom0047 chi) ∨
      (Fin15AnchoredAtom0048 chi)) ∨
      ((Fin15AnchoredAtom0049 chi) ∨
      (Fin15AnchoredAtom0050 chi)))) ∨
      ((((Fin15AnchoredAtom0051 chi) ∨
      (Fin15AnchoredAtom0052 chi)) ∨
      ((Fin15AnchoredAtom0053 chi) ∨
      (Fin15AnchoredAtom0054 chi))) ∨
      (((Fin15AnchoredAtom0055 chi) ∨
      (Fin15AnchoredAtom0056 chi)) ∨
      ((Fin15AnchoredAtom0057 chi) ∨
      (Fin15AnchoredAtom0058 chi)))))) ∨
      ((((((Fin15AnchoredAtom0059 chi) ∨
      (Fin15AnchoredAtom0060 chi)) ∨
      ((Fin15AnchoredAtom0061 chi) ∨
      (Fin15AnchoredAtom0062 chi))) ∨
      (((Fin15AnchoredAtom0063 chi) ∨
      (Fin15AnchoredAtom0064 chi)) ∨
      ((Fin15AnchoredAtom0065 chi) ∨
      (Fin15AnchoredAtom0066 chi)))) ∨
      ((((Fin15AnchoredAtom0067 chi) ∨
      (Fin15AnchoredAtom0068 chi)) ∨
      ((Fin15AnchoredAtom0069 chi) ∨
      (Fin15AnchoredAtom0070 chi))) ∨
      (((Fin15AnchoredAtom0071 chi) ∨
      (Fin15AnchoredAtom0072 chi)) ∨
      ((Fin15AnchoredAtom0074 chi) ∨
      (Fin15AnchoredAtom0075 chi))))) ∨
      (((((Fin15AnchoredAtom0076 chi) ∨
      (Fin15AnchoredAtom0077 chi)) ∨
      ((Fin15AnchoredAtom0078 chi) ∨
      (Fin15AnchoredAtom0079 chi))) ∨
      (((Fin15AnchoredAtom0080 chi) ∨
      (Fin15AnchoredAtom0081 chi)) ∨
      ((Fin15AnchoredAtom0082 chi) ∨
      (Fin15AnchoredAtom0083 chi)))) ∨
      ((((Fin15AnchoredAtom0084 chi) ∨
      (Fin15AnchoredAtom0085 chi)) ∨
      ((Fin15AnchoredAtom0086 chi) ∨
      (Fin15AnchoredAtom0087 chi))) ∨
      (((Fin15AnchoredAtom0088 chi) ∨
      (Fin15AnchoredAtom0089 chi)) ∨
      ((Fin15AnchoredAtom0090 chi) ∨
      (Fin15AnchoredAtom0091 chi)))))))))) := by
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
                exact fin15Anchored_clause32056 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32057 chi hno hbad
                ·
                  exact fin15Anchored_clause32058 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32059 chi hno hbad
                ·
                  exact fin15Anchored_clause32060 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32061 chi hno hbad
                ·
                  exact fin15Anchored_clause32062 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32063 chi hno hbad
                ·
                  exact fin15Anchored_clause32064 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32065 chi hno hbad
                ·
                  exact fin15Anchored_clause32066 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32067 chi hno hbad
                ·
                  exact fin15Anchored_clause32068 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32069 chi hno hbad
                ·
                  exact fin15Anchored_clause32070 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32071 chi hno hbad
                ·
                  exact fin15Anchored_clause32072 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32073 chi hno hbad
                ·
                  exact fin15Anchored_clause32074 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32075 chi hno hbad
                ·
                  exact fin15Anchored_clause32076 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32077 chi hno hbad
                ·
                  exact fin15Anchored_clause32078 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32079 chi hno hbad
                ·
                  exact fin15Anchored_clause32080 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32081 chi hno hbad
                ·
                  exact fin15Anchored_clause32082 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32083 chi hno hbad
                ·
                  exact fin15Anchored_clause32084 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32085 chi hno hbad
                ·
                  exact fin15Anchored_clause32086 chi hno hbad
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
                  exact fin15Anchored_clause32087 chi hno hbad
                ·
                  exact fin15Anchored_clause32088 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32089 chi hno hbad
                ·
                  exact fin15Anchored_clause32090 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32091 chi hno hbad
                ·
                  exact fin15Anchored_clause32092 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32093 chi hno hbad
                ·
                  exact fin15Anchored_clause32094 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32095 chi hno hbad
                ·
                  exact fin15Anchored_clause32096 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32097 chi hno hbad
                ·
                  exact fin15Anchored_clause32098 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32099 chi hno hbad
                ·
                  exact fin15Anchored_clause32100 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32101 chi hno hbad
                ·
                  exact fin15Anchored_clause32102 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32103 chi hno hbad
                ·
                  exact fin15Anchored_clause32104 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32105 chi hno hbad
                ·
                  exact fin15Anchored_clause32106 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32107 chi hno hbad
                ·
                  exact fin15Anchored_clause32108 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32109 chi hno hbad
                ·
                  exact fin15Anchored_clause32110 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32111 chi hno hbad
                ·
                  exact fin15Anchored_clause32112 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32113 chi hno hbad
                ·
                  exact fin15Anchored_clause32114 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32115 chi hno hbad
                ·
                  exact fin15Anchored_clause32116 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32117 chi hno hbad
                ·
                  exact fin15Anchored_clause32118 chi hno hbad
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
                exact fin15Anchored_clause32119 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32120 chi hno hbad
                ·
                  exact fin15Anchored_clause32121 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32122 chi hno hbad
                ·
                  exact fin15Anchored_clause32123 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32124 chi hno hbad
                ·
                  exact fin15Anchored_clause32125 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32126 chi hno hbad
                ·
                  exact fin15Anchored_clause32127 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32128 chi hno hbad
                ·
                  exact fin15Anchored_clause32129 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32130 chi hno hbad
                ·
                  exact fin15Anchored_clause32131 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32132 chi hno hbad
                ·
                  exact fin15Anchored_clause32133 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32134 chi hno hbad
                ·
                  exact fin15Anchored_clause32135 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32136 chi hno hbad
                ·
                  exact fin15Anchored_clause32137 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32138 chi hno hbad
                ·
                  exact fin15Anchored_clause32139 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32140 chi hno hbad
                ·
                  exact fin15Anchored_clause32141 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32142 chi hno hbad
                ·
                  exact fin15Anchored_clause32143 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32144 chi hno hbad
                ·
                  exact fin15Anchored_clause32145 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32146 chi hno hbad
                ·
                  exact fin15Anchored_clause32147 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32148 chi hno hbad
                ·
                  exact fin15Anchored_clause32149 chi hno hbad
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
                  exact fin15Anchored_clause32150 chi hno hbad
                ·
                  exact fin15Anchored_clause32151 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32152 chi hno hbad
                ·
                  exact fin15Anchored_clause32153 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32154 chi hno hbad
                ·
                  exact fin15Anchored_clause32155 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32156 chi hno hbad
                ·
                  exact fin15Anchored_clause32157 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32158 chi hno hbad
                ·
                  exact fin15Anchored_clause32159 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32160 chi hno hbad
                ·
                  exact fin15Anchored_clause32161 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32162 chi hno hbad
                ·
                  exact fin15Anchored_clause32163 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32164 chi hno hbad
                ·
                  exact fin15Anchored_clause32165 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32166 chi hno hbad
                ·
                  exact fin15Anchored_clause32167 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32168 chi hno hbad
                ·
                  exact fin15Anchored_clause32169 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32170 chi hno hbad
                ·
                  exact fin15Anchored_clause32171 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32172 chi hno hbad
                ·
                  exact fin15Anchored_clause32173 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32174 chi hno hbad
                ·
                  exact fin15Anchored_clause32175 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32176 chi hno hbad
                ·
                  exact fin15Anchored_clause32177 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32178 chi hno hbad
                ·
                  exact fin15Anchored_clause32179 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32180 chi hno hbad
                ·
                  exact fin15Anchored_clause32181 chi hno hbad
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
                exact fin15Anchored_clause32182 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32183 chi hno hbad
                ·
                  exact fin15Anchored_clause32184 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32185 chi hno hbad
                ·
                  exact fin15Anchored_clause32186 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32187 chi hno hbad
                ·
                  exact fin15Anchored_clause32188 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32189 chi hno hbad
                ·
                  exact fin15Anchored_clause32190 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32191 chi hno hbad
                ·
                  exact fin15Anchored_clause32192 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32193 chi hno hbad
                ·
                  exact fin15Anchored_clause32194 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32195 chi hno hbad
                ·
                  exact fin15Anchored_clause32196 chi hno hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32197 chi hno hbad
                ·
                  exact fin15Anchored_clause32198 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32199 chi hno hbad
                ·
                  exact fin15Anchored_clause32200 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32201 chi hno hbad
                ·
                  exact fin15Anchored_clause32202 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32203 chi hno hbad
                ·
                  exact fin15Anchored_clause32204 chi hno hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32205 chi hno hbad
                ·
                  exact fin15Anchored_clause32206 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32207 chi hno hbad
                ·
                  exact fin15Anchored_clause32208 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32209 chi hno hbad
                ·
                  exact fin15Anchored_clause32210 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32211 chi hno hbad
                ·
                  exact fin15Anchored_clause32212 chi hno hbad
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
                  exact fin15Anchored_clause32213 chi hno hbad
                ·
                  exact fin15Anchored_clause32214 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32215 chi hno hbad
                ·
                  exact fin15Anchored_clause32216 chi hno hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32217 chi hno hbad
                ·
                  exact fin15Anchored_clause32218 chi hno hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32219 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32220 chi hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32221 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32222 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32223 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32224 chi hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32225 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32226 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32227 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32228 chi hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32229 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32230 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32231 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32232 chi hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32233 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32234 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32235 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32236 chi hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32237 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32238 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32239 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32240 chi hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32241 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32242 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32243 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32244 chi hanchor hbad
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
                  exact fin15Anchored_clause32245 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32246 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32247 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32248 chi hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32249 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32250 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32251 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32252 chi hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32253 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32254 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32255 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32256 chi hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32257 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32258 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32259 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32260 chi hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32261 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32262 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32263 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32264 chi hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32265 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32266 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32267 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32268 chi hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32269 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32270 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32271 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32272 chi hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32273 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32274 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32275 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32276 chi hanchor hbad
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
                  exact fin15Anchored_clause32277 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32278 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32279 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32280 chi hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32281 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32282 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32283 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32284 chi hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32285 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32286 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32287 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32288 chi hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32289 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32290 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32291 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32292 chi hanchor hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32293 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32294 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32295 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32296 chi hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32297 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32298 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32299 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32300 chi hanchor hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32301 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32302 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32303 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32304 chi hanchor hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32305 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32306 chi hanchor hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause32307 chi hanchor hbad
                ·
                  exact fin15Anchored_clause32308 chi hanchor hbad

end ErdosSzekeres

end
