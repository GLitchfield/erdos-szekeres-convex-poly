module

public import ErdosSzekeres.Fin15AnchoredClauseChunk234
public import ErdosSzekeres.Fin15AnchoredClauseChunk235
public import ErdosSzekeres.Fin15AnchoredClauseChunk236

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 119. -/

theorem fin15Anchored_rejectSemanticSegment119
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom3714 chi ∧
      Fin15AnchoredAtom3716 chi ∧
      Fin15AnchoredAtom3736 chi ∧
      Fin15AnchoredAtom3785 chi ∧
      Fin15AnchoredAtom3869 chi ∧
      Fin15AnchoredAtom4409 chi) ∨
      ((Fin15AnchoredAtom3715 chi ∧
      Fin15AnchoredAtom3716 chi ∧
      Fin15AnchoredAtom3737 chi ∧
      Fin15AnchoredAtom3786 chi ∧
      Fin15AnchoredAtom3870 chi ∧
      Fin15AnchoredAtom4410 chi) ∨
      (Fin15AnchoredAtom3723 chi ∧
      Fin15AnchoredAtom3725 chi ∧
      Fin15AnchoredAtom3729 chi ∧
      Fin15AnchoredAtom3803 chi ∧
      Fin15AnchoredAtom3887 chi ∧
      Fin15AnchoredAtom4427 chi))) ∨
      (((Fin15AnchoredAtom3723 chi ∧
      Fin15AnchoredAtom3726 chi ∧
      Fin15AnchoredAtom3730 chi ∧
      Fin15AnchoredAtom3804 chi ∧
      Fin15AnchoredAtom3888 chi ∧
      Fin15AnchoredAtom4428 chi) ∨
      (Fin15AnchoredAtom3723 chi ∧
      Fin15AnchoredAtom3727 chi ∧
      Fin15AnchoredAtom3731 chi ∧
      Fin15AnchoredAtom3805 chi ∧
      Fin15AnchoredAtom3889 chi ∧
      Fin15AnchoredAtom4429 chi)) ∨
      ((Fin15AnchoredAtom3725 chi ∧
      Fin15AnchoredAtom3726 chi ∧
      Fin15AnchoredAtom3735 chi ∧
      Fin15AnchoredAtom3809 chi ∧
      Fin15AnchoredAtom3893 chi ∧
      Fin15AnchoredAtom4433 chi) ∨
      (Fin15AnchoredAtom3725 chi ∧
      Fin15AnchoredAtom3727 chi ∧
      Fin15AnchoredAtom3736 chi ∧
      Fin15AnchoredAtom3810 chi ∧
      Fin15AnchoredAtom3894 chi ∧
      Fin15AnchoredAtom4434 chi)))) ∨
      ((((Fin15AnchoredAtom3726 chi ∧
      Fin15AnchoredAtom3727 chi ∧
      Fin15AnchoredAtom3737 chi ∧
      Fin15AnchoredAtom3811 chi ∧
      Fin15AnchoredAtom3895 chi ∧
      Fin15AnchoredAtom4435 chi) ∨
      (Fin15AnchoredAtom3729 chi ∧
      Fin15AnchoredAtom3730 chi ∧
      Fin15AnchoredAtom3735 chi ∧
      Fin15AnchoredAtom3815 chi ∧
      Fin15AnchoredAtom3899 chi ∧
      Fin15AnchoredAtom4439 chi)) ∨
      ((Fin15AnchoredAtom3729 chi ∧
      Fin15AnchoredAtom3731 chi ∧
      Fin15AnchoredAtom3736 chi ∧
      Fin15AnchoredAtom3816 chi ∧
      Fin15AnchoredAtom3900 chi ∧
      Fin15AnchoredAtom4440 chi) ∨
      (Fin15AnchoredAtom3730 chi ∧
      Fin15AnchoredAtom3731 chi ∧
      Fin15AnchoredAtom3737 chi ∧
      Fin15AnchoredAtom3817 chi ∧
      Fin15AnchoredAtom3901 chi ∧
      Fin15AnchoredAtom4441 chi))) ∨
      (((Fin15AnchoredAtom3735 chi ∧
      Fin15AnchoredAtom3736 chi ∧
      Fin15AnchoredAtom3737 chi ∧
      Fin15AnchoredAtom3821 chi ∧
      Fin15AnchoredAtom3905 chi ∧
      Fin15AnchoredAtom4445 chi) ∨
      (Fin15AnchoredAtom3738 chi ∧
      Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom3745 chi ∧
      Fin15AnchoredAtom3766 chi ∧
      Fin15AnchoredAtom3906 chi ∧
      Fin15AnchoredAtom4446 chi)) ∨
      ((Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom3740 chi ∧
      Fin15AnchoredAtom3751 chi ∧
      Fin15AnchoredAtom3772 chi ∧
      Fin15AnchoredAtom3912 chi ∧
      Fin15AnchoredAtom4452 chi) ∨
      (Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom3741 chi ∧
      Fin15AnchoredAtom3752 chi ∧
      Fin15AnchoredAtom3773 chi ∧
      Fin15AnchoredAtom3913 chi ∧
      Fin15AnchoredAtom4453 chi))))) ∨
      (((((Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom3742 chi ∧
      Fin15AnchoredAtom3753 chi ∧
      Fin15AnchoredAtom3774 chi ∧
      Fin15AnchoredAtom3914 chi ∧
      Fin15AnchoredAtom4454 chi) ∨
      (Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom3743 chi ∧
      Fin15AnchoredAtom3754 chi ∧
      Fin15AnchoredAtom3775 chi ∧
      Fin15AnchoredAtom3915 chi ∧
      Fin15AnchoredAtom4455 chi)) ∨
      ((Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom3744 chi ∧
      Fin15AnchoredAtom3755 chi ∧
      Fin15AnchoredAtom3776 chi ∧
      Fin15AnchoredAtom3916 chi ∧
      Fin15AnchoredAtom4456 chi) ∨
      (Fin15AnchoredAtom3740 chi ∧
      Fin15AnchoredAtom3742 chi ∧
      Fin15AnchoredAtom3757 chi ∧
      Fin15AnchoredAtom3778 chi ∧
      Fin15AnchoredAtom3918 chi ∧
      Fin15AnchoredAtom4458 chi))) ∨
      (((Fin15AnchoredAtom3740 chi ∧
      Fin15AnchoredAtom3743 chi ∧
      Fin15AnchoredAtom3758 chi ∧
      Fin15AnchoredAtom3779 chi ∧
      Fin15AnchoredAtom3919 chi ∧
      Fin15AnchoredAtom4459 chi) ∨
      (Fin15AnchoredAtom3740 chi ∧
      Fin15AnchoredAtom3744 chi ∧
      Fin15AnchoredAtom3759 chi ∧
      Fin15AnchoredAtom3780 chi ∧
      Fin15AnchoredAtom3920 chi ∧
      Fin15AnchoredAtom4460 chi)) ∨
      ((Fin15AnchoredAtom3742 chi ∧
      Fin15AnchoredAtom3743 chi ∧
      Fin15AnchoredAtom3763 chi ∧
      Fin15AnchoredAtom3784 chi ∧
      Fin15AnchoredAtom3924 chi ∧
      Fin15AnchoredAtom4464 chi) ∨
      (Fin15AnchoredAtom3742 chi ∧
      Fin15AnchoredAtom3744 chi ∧
      Fin15AnchoredAtom3764 chi ∧
      Fin15AnchoredAtom3785 chi ∧
      Fin15AnchoredAtom3925 chi ∧
      Fin15AnchoredAtom4465 chi)))) ∨
      ((((Fin15AnchoredAtom3743 chi ∧
      Fin15AnchoredAtom3744 chi ∧
      Fin15AnchoredAtom3765 chi ∧
      Fin15AnchoredAtom3786 chi ∧
      Fin15AnchoredAtom3926 chi ∧
      Fin15AnchoredAtom4466 chi) ∨
      (Fin15AnchoredAtom3751 chi ∧
      Fin15AnchoredAtom3753 chi ∧
      Fin15AnchoredAtom3757 chi ∧
      Fin15AnchoredAtom3803 chi ∧
      Fin15AnchoredAtom3943 chi ∧
      Fin15AnchoredAtom4483 chi)) ∨
      ((Fin15AnchoredAtom3751 chi ∧
      Fin15AnchoredAtom3754 chi ∧
      Fin15AnchoredAtom3758 chi ∧
      Fin15AnchoredAtom3804 chi ∧
      Fin15AnchoredAtom3944 chi ∧
      Fin15AnchoredAtom4484 chi) ∨
      (Fin15AnchoredAtom3751 chi ∧
      Fin15AnchoredAtom3755 chi ∧
      Fin15AnchoredAtom3759 chi ∧
      Fin15AnchoredAtom3805 chi ∧
      Fin15AnchoredAtom3945 chi ∧
      Fin15AnchoredAtom4485 chi))) ∨
      (((Fin15AnchoredAtom3753 chi ∧
      Fin15AnchoredAtom3754 chi ∧
      Fin15AnchoredAtom3763 chi ∧
      Fin15AnchoredAtom3809 chi ∧
      Fin15AnchoredAtom3949 chi ∧
      Fin15AnchoredAtom4489 chi) ∨
      (Fin15AnchoredAtom3753 chi ∧
      Fin15AnchoredAtom3755 chi ∧
      Fin15AnchoredAtom3764 chi ∧
      Fin15AnchoredAtom3810 chi ∧
      Fin15AnchoredAtom3950 chi ∧
      Fin15AnchoredAtom4490 chi)) ∨
      ((Fin15AnchoredAtom3754 chi ∧
      Fin15AnchoredAtom3755 chi ∧
      Fin15AnchoredAtom3765 chi ∧
      Fin15AnchoredAtom3811 chi ∧
      Fin15AnchoredAtom3951 chi ∧
      Fin15AnchoredAtom4491 chi) ∨
      (Fin15AnchoredAtom3757 chi ∧
      Fin15AnchoredAtom3758 chi ∧
      Fin15AnchoredAtom3763 chi ∧
      Fin15AnchoredAtom3815 chi ∧
      Fin15AnchoredAtom3955 chi ∧
      Fin15AnchoredAtom4495 chi)))))) ∨
      ((((((Fin15AnchoredAtom3757 chi ∧
      Fin15AnchoredAtom3759 chi ∧
      Fin15AnchoredAtom3764 chi ∧
      Fin15AnchoredAtom3816 chi ∧
      Fin15AnchoredAtom3956 chi ∧
      Fin15AnchoredAtom4496 chi) ∨
      (Fin15AnchoredAtom3758 chi ∧
      Fin15AnchoredAtom3759 chi ∧
      Fin15AnchoredAtom3765 chi ∧
      Fin15AnchoredAtom3817 chi ∧
      Fin15AnchoredAtom3957 chi ∧
      Fin15AnchoredAtom4497 chi)) ∨
      ((Fin15AnchoredAtom3763 chi ∧
      Fin15AnchoredAtom3764 chi ∧
      Fin15AnchoredAtom3765 chi ∧
      Fin15AnchoredAtom3821 chi ∧
      Fin15AnchoredAtom3961 chi ∧
      Fin15AnchoredAtom4501 chi) ∨
      (Fin15AnchoredAtom3772 chi ∧
      Fin15AnchoredAtom3774 chi ∧
      Fin15AnchoredAtom3778 chi ∧
      Fin15AnchoredAtom3803 chi ∧
      Fin15AnchoredAtom3978 chi ∧
      Fin15AnchoredAtom4518 chi))) ∨
      (((Fin15AnchoredAtom3772 chi ∧
      Fin15AnchoredAtom3775 chi ∧
      Fin15AnchoredAtom3779 chi ∧
      Fin15AnchoredAtom3804 chi ∧
      Fin15AnchoredAtom3979 chi ∧
      Fin15AnchoredAtom4519 chi) ∨
      (Fin15AnchoredAtom3772 chi ∧
      Fin15AnchoredAtom3776 chi ∧
      Fin15AnchoredAtom3780 chi ∧
      Fin15AnchoredAtom3805 chi ∧
      Fin15AnchoredAtom3980 chi ∧
      Fin15AnchoredAtom4520 chi)) ∨
      ((Fin15AnchoredAtom3774 chi ∧
      Fin15AnchoredAtom3775 chi ∧
      Fin15AnchoredAtom3784 chi ∧
      Fin15AnchoredAtom3809 chi ∧
      Fin15AnchoredAtom3984 chi ∧
      Fin15AnchoredAtom4524 chi) ∨
      (Fin15AnchoredAtom3774 chi ∧
      Fin15AnchoredAtom3776 chi ∧
      Fin15AnchoredAtom3785 chi ∧
      Fin15AnchoredAtom3810 chi ∧
      Fin15AnchoredAtom3985 chi ∧
      Fin15AnchoredAtom4525 chi)))) ∨
      ((((Fin15AnchoredAtom3775 chi ∧
      Fin15AnchoredAtom3776 chi ∧
      Fin15AnchoredAtom3786 chi ∧
      Fin15AnchoredAtom3811 chi ∧
      Fin15AnchoredAtom3986 chi ∧
      Fin15AnchoredAtom4526 chi) ∨
      (Fin15AnchoredAtom3778 chi ∧
      Fin15AnchoredAtom3779 chi ∧
      Fin15AnchoredAtom3784 chi ∧
      Fin15AnchoredAtom3815 chi ∧
      Fin15AnchoredAtom3990 chi ∧
      Fin15AnchoredAtom4530 chi)) ∨
      ((Fin15AnchoredAtom3778 chi ∧
      Fin15AnchoredAtom3780 chi ∧
      Fin15AnchoredAtom3785 chi ∧
      Fin15AnchoredAtom3816 chi ∧
      Fin15AnchoredAtom3991 chi ∧
      Fin15AnchoredAtom4531 chi) ∨
      (Fin15AnchoredAtom3779 chi ∧
      Fin15AnchoredAtom3780 chi ∧
      Fin15AnchoredAtom3786 chi ∧
      Fin15AnchoredAtom3817 chi ∧
      Fin15AnchoredAtom3992 chi ∧
      Fin15AnchoredAtom4532 chi))) ∨
      (((Fin15AnchoredAtom3784 chi ∧
      Fin15AnchoredAtom3785 chi ∧
      Fin15AnchoredAtom3786 chi ∧
      Fin15AnchoredAtom3821 chi ∧
      Fin15AnchoredAtom3996 chi ∧
      Fin15AnchoredAtom4536 chi) ∨
      (Fin15AnchoredAtom3787 chi ∧
      Fin15AnchoredAtom3789 chi ∧
      Fin15AnchoredAtom3793 chi ∧
      Fin15AnchoredAtom3803 chi ∧
      Fin15AnchoredAtom3998 chi ∧
      Fin15AnchoredAtom4538 chi)) ∨
      ((Fin15AnchoredAtom3793 chi ∧
      Fin15AnchoredAtom3794 chi ∧
      Fin15AnchoredAtom3799 chi ∧
      Fin15AnchoredAtom3815 chi ∧
      Fin15AnchoredAtom4010 chi ∧
      Fin15AnchoredAtom4550 chi) ∨
      (Fin15AnchoredAtom3803 chi ∧
      Fin15AnchoredAtom3804 chi ∧
      Fin15AnchoredAtom3809 chi ∧
      Fin15AnchoredAtom3815 chi ∧
      Fin15AnchoredAtom4020 chi ∧
      Fin15AnchoredAtom4560 chi))))) ∨
      (((((Fin15AnchoredAtom3803 chi ∧
      Fin15AnchoredAtom3805 chi ∧
      Fin15AnchoredAtom3810 chi ∧
      Fin15AnchoredAtom3816 chi ∧
      Fin15AnchoredAtom4021 chi ∧
      Fin15AnchoredAtom4561 chi) ∨
      (Fin15AnchoredAtom3804 chi ∧
      Fin15AnchoredAtom3805 chi ∧
      Fin15AnchoredAtom3811 chi ∧
      Fin15AnchoredAtom3817 chi ∧
      Fin15AnchoredAtom4022 chi ∧
      Fin15AnchoredAtom4562 chi)) ∨
      ((Fin15AnchoredAtom3809 chi ∧
      Fin15AnchoredAtom3810 chi ∧
      Fin15AnchoredAtom3811 chi ∧
      Fin15AnchoredAtom3821 chi ∧
      Fin15AnchoredAtom4026 chi ∧
      Fin15AnchoredAtom4566 chi) ∨
      (Fin15AnchoredAtom3815 chi ∧
      Fin15AnchoredAtom3816 chi ∧
      Fin15AnchoredAtom3817 chi ∧
      Fin15AnchoredAtom3821 chi ∧
      Fin15AnchoredAtom4030 chi ∧
      Fin15AnchoredAtom4570 chi))) ∨
      (((Fin15AnchoredAtom3823 chi ∧
      Fin15AnchoredAtom3824 chi ∧
      Fin15AnchoredAtom3835 chi ∧
      Fin15AnchoredAtom3856 chi ∧
      Fin15AnchoredAtom3912 chi ∧
      Fin15AnchoredAtom4578 chi) ∨
      (Fin15AnchoredAtom3823 chi ∧
      Fin15AnchoredAtom3826 chi ∧
      Fin15AnchoredAtom3837 chi ∧
      Fin15AnchoredAtom3858 chi ∧
      Fin15AnchoredAtom3914 chi ∧
      Fin15AnchoredAtom4580 chi)) ∨
      ((Fin15AnchoredAtom3823 chi ∧
      Fin15AnchoredAtom3827 chi ∧
      Fin15AnchoredAtom3838 chi ∧
      Fin15AnchoredAtom3859 chi ∧
      Fin15AnchoredAtom3915 chi ∧
      Fin15AnchoredAtom4581 chi) ∨
      (Fin15AnchoredAtom3823 chi ∧
      Fin15AnchoredAtom3828 chi ∧
      Fin15AnchoredAtom3839 chi ∧
      Fin15AnchoredAtom3860 chi ∧
      Fin15AnchoredAtom3916 chi ∧
      Fin15AnchoredAtom4582 chi)))) ∨
      ((((Fin15AnchoredAtom3824 chi ∧
      Fin15AnchoredAtom3825 chi ∧
      Fin15AnchoredAtom3840 chi ∧
      Fin15AnchoredAtom3861 chi ∧
      Fin15AnchoredAtom3917 chi ∧
      Fin15AnchoredAtom4583 chi) ∨
      (Fin15AnchoredAtom3824 chi ∧
      Fin15AnchoredAtom3826 chi ∧
      Fin15AnchoredAtom3841 chi ∧
      Fin15AnchoredAtom3862 chi ∧
      Fin15AnchoredAtom3918 chi ∧
      Fin15AnchoredAtom4584 chi)) ∨
      ((Fin15AnchoredAtom3824 chi ∧
      Fin15AnchoredAtom3827 chi ∧
      Fin15AnchoredAtom3842 chi ∧
      Fin15AnchoredAtom3863 chi ∧
      Fin15AnchoredAtom3919 chi ∧
      Fin15AnchoredAtom4585 chi) ∨
      (Fin15AnchoredAtom3824 chi ∧
      Fin15AnchoredAtom3828 chi ∧
      Fin15AnchoredAtom3843 chi ∧
      Fin15AnchoredAtom3864 chi ∧
      Fin15AnchoredAtom3920 chi ∧
      Fin15AnchoredAtom4586 chi))) ∨
      (((Fin15AnchoredAtom3826 chi ∧
      Fin15AnchoredAtom3827 chi ∧
      Fin15AnchoredAtom3847 chi ∧
      Fin15AnchoredAtom3868 chi ∧
      Fin15AnchoredAtom3924 chi ∧
      Fin15AnchoredAtom4590 chi) ∨
      (Fin15AnchoredAtom3826 chi ∧
      Fin15AnchoredAtom3828 chi ∧
      Fin15AnchoredAtom3848 chi ∧
      Fin15AnchoredAtom3869 chi ∧
      Fin15AnchoredAtom3925 chi ∧
      Fin15AnchoredAtom4591 chi)) ∨
      ((Fin15AnchoredAtom3827 chi ∧
      Fin15AnchoredAtom3828 chi ∧
      Fin15AnchoredAtom3849 chi ∧
      Fin15AnchoredAtom3870 chi ∧
      Fin15AnchoredAtom3926 chi ∧
      Fin15AnchoredAtom4592 chi) ∨
      (Fin15AnchoredAtom3835 chi ∧
      Fin15AnchoredAtom3837 chi ∧
      Fin15AnchoredAtom3841 chi ∧
      Fin15AnchoredAtom3887 chi ∧
      Fin15AnchoredAtom3943 chi ∧
      Fin15AnchoredAtom4609 chi))))))) ∨
      ((((((Fin15AnchoredAtom3835 chi ∧
      Fin15AnchoredAtom3838 chi ∧
      Fin15AnchoredAtom3842 chi ∧
      Fin15AnchoredAtom3888 chi ∧
      Fin15AnchoredAtom3944 chi ∧
      Fin15AnchoredAtom4610 chi) ∨
      ((Fin15AnchoredAtom3835 chi ∧
      Fin15AnchoredAtom3839 chi ∧
      Fin15AnchoredAtom3843 chi ∧
      Fin15AnchoredAtom3889 chi ∧
      Fin15AnchoredAtom3945 chi ∧
      Fin15AnchoredAtom4611 chi) ∨
      (Fin15AnchoredAtom3837 chi ∧
      Fin15AnchoredAtom3838 chi ∧
      Fin15AnchoredAtom3847 chi ∧
      Fin15AnchoredAtom3893 chi ∧
      Fin15AnchoredAtom3949 chi ∧
      Fin15AnchoredAtom4615 chi))) ∨
      (((Fin15AnchoredAtom3837 chi ∧
      Fin15AnchoredAtom3839 chi ∧
      Fin15AnchoredAtom3848 chi ∧
      Fin15AnchoredAtom3894 chi ∧
      Fin15AnchoredAtom3950 chi ∧
      Fin15AnchoredAtom4616 chi) ∨
      (Fin15AnchoredAtom3838 chi ∧
      Fin15AnchoredAtom3839 chi ∧
      Fin15AnchoredAtom3849 chi ∧
      Fin15AnchoredAtom3895 chi ∧
      Fin15AnchoredAtom3951 chi ∧
      Fin15AnchoredAtom4617 chi)) ∨
      ((Fin15AnchoredAtom3840 chi ∧
      Fin15AnchoredAtom3841 chi ∧
      Fin15AnchoredAtom3844 chi ∧
      Fin15AnchoredAtom3896 chi ∧
      Fin15AnchoredAtom3952 chi ∧
      Fin15AnchoredAtom4618 chi) ∨
      (Fin15AnchoredAtom3841 chi ∧
      Fin15AnchoredAtom3842 chi ∧
      Fin15AnchoredAtom3847 chi ∧
      Fin15AnchoredAtom3899 chi ∧
      Fin15AnchoredAtom3955 chi ∧
      Fin15AnchoredAtom4621 chi)))) ∨
      ((((Fin15AnchoredAtom3841 chi ∧
      Fin15AnchoredAtom3843 chi ∧
      Fin15AnchoredAtom3848 chi ∧
      Fin15AnchoredAtom3900 chi ∧
      Fin15AnchoredAtom3956 chi ∧
      Fin15AnchoredAtom4622 chi) ∨
      (Fin15AnchoredAtom3842 chi ∧
      Fin15AnchoredAtom3843 chi ∧
      Fin15AnchoredAtom3849 chi ∧
      Fin15AnchoredAtom3901 chi ∧
      Fin15AnchoredAtom3957 chi ∧
      Fin15AnchoredAtom4623 chi)) ∨
      ((Fin15AnchoredAtom3847 chi ∧
      Fin15AnchoredAtom3848 chi ∧
      Fin15AnchoredAtom3849 chi ∧
      Fin15AnchoredAtom3905 chi ∧
      Fin15AnchoredAtom3961 chi ∧
      Fin15AnchoredAtom4627 chi) ∨
      (Fin15AnchoredAtom3856 chi ∧
      Fin15AnchoredAtom3858 chi ∧
      Fin15AnchoredAtom3862 chi ∧
      Fin15AnchoredAtom3887 chi ∧
      Fin15AnchoredAtom3978 chi ∧
      Fin15AnchoredAtom4644 chi))) ∨
      (((Fin15AnchoredAtom3856 chi ∧
      Fin15AnchoredAtom3859 chi ∧
      Fin15AnchoredAtom3863 chi ∧
      Fin15AnchoredAtom3888 chi ∧
      Fin15AnchoredAtom3979 chi ∧
      Fin15AnchoredAtom4645 chi) ∨
      (Fin15AnchoredAtom3856 chi ∧
      Fin15AnchoredAtom3860 chi ∧
      Fin15AnchoredAtom3864 chi ∧
      Fin15AnchoredAtom3889 chi ∧
      Fin15AnchoredAtom3980 chi ∧
      Fin15AnchoredAtom4646 chi)) ∨
      ((Fin15AnchoredAtom3858 chi ∧
      Fin15AnchoredAtom3859 chi ∧
      Fin15AnchoredAtom3868 chi ∧
      Fin15AnchoredAtom3893 chi ∧
      Fin15AnchoredAtom3984 chi ∧
      Fin15AnchoredAtom4650 chi) ∨
      (Fin15AnchoredAtom3858 chi ∧
      Fin15AnchoredAtom3860 chi ∧
      Fin15AnchoredAtom3869 chi ∧
      Fin15AnchoredAtom3894 chi ∧
      Fin15AnchoredAtom3985 chi ∧
      Fin15AnchoredAtom4651 chi))))) ∨
      (((((Fin15AnchoredAtom3859 chi ∧
      Fin15AnchoredAtom3860 chi ∧
      Fin15AnchoredAtom3870 chi ∧
      Fin15AnchoredAtom3895 chi ∧
      Fin15AnchoredAtom3986 chi ∧
      Fin15AnchoredAtom4652 chi) ∨
      (Fin15AnchoredAtom3862 chi ∧
      Fin15AnchoredAtom3863 chi ∧
      Fin15AnchoredAtom3868 chi ∧
      Fin15AnchoredAtom3899 chi ∧
      Fin15AnchoredAtom3990 chi ∧
      Fin15AnchoredAtom4656 chi)) ∨
      ((Fin15AnchoredAtom3862 chi ∧
      Fin15AnchoredAtom3864 chi ∧
      Fin15AnchoredAtom3869 chi ∧
      Fin15AnchoredAtom3900 chi ∧
      Fin15AnchoredAtom3991 chi ∧
      Fin15AnchoredAtom4657 chi) ∨
      (Fin15AnchoredAtom3863 chi ∧
      Fin15AnchoredAtom3864 chi ∧
      Fin15AnchoredAtom3870 chi ∧
      Fin15AnchoredAtom3901 chi ∧
      Fin15AnchoredAtom3992 chi ∧
      Fin15AnchoredAtom4658 chi))) ∨
      (((Fin15AnchoredAtom3868 chi ∧
      Fin15AnchoredAtom3869 chi ∧
      Fin15AnchoredAtom3870 chi ∧
      Fin15AnchoredAtom3905 chi ∧
      Fin15AnchoredAtom3996 chi ∧
      Fin15AnchoredAtom4662 chi) ∨
      (Fin15AnchoredAtom3887 chi ∧
      Fin15AnchoredAtom3888 chi ∧
      Fin15AnchoredAtom3893 chi ∧
      Fin15AnchoredAtom3899 chi ∧
      Fin15AnchoredAtom4020 chi ∧
      Fin15AnchoredAtom4686 chi)) ∨
      ((Fin15AnchoredAtom3887 chi ∧
      Fin15AnchoredAtom3889 chi ∧
      Fin15AnchoredAtom3894 chi ∧
      Fin15AnchoredAtom3900 chi ∧
      Fin15AnchoredAtom4021 chi ∧
      Fin15AnchoredAtom4687 chi) ∨
      (Fin15AnchoredAtom3888 chi ∧
      Fin15AnchoredAtom3889 chi ∧
      Fin15AnchoredAtom3895 chi ∧
      Fin15AnchoredAtom3901 chi ∧
      Fin15AnchoredAtom4022 chi ∧
      Fin15AnchoredAtom4688 chi)))) ∨
      ((((Fin15AnchoredAtom3893 chi ∧
      Fin15AnchoredAtom3894 chi ∧
      Fin15AnchoredAtom3895 chi ∧
      Fin15AnchoredAtom3905 chi ∧
      Fin15AnchoredAtom4026 chi ∧
      Fin15AnchoredAtom4692 chi) ∨
      (Fin15AnchoredAtom3899 chi ∧
      Fin15AnchoredAtom3900 chi ∧
      Fin15AnchoredAtom3901 chi ∧
      Fin15AnchoredAtom3905 chi ∧
      Fin15AnchoredAtom4030 chi ∧
      Fin15AnchoredAtom4696 chi)) ∨
      ((Fin15AnchoredAtom3912 chi ∧
      Fin15AnchoredAtom3914 chi ∧
      Fin15AnchoredAtom3918 chi ∧
      Fin15AnchoredAtom3943 chi ∧
      Fin15AnchoredAtom3978 chi ∧
      Fin15AnchoredAtom4714 chi) ∨
      (Fin15AnchoredAtom3912 chi ∧
      Fin15AnchoredAtom3915 chi ∧
      Fin15AnchoredAtom3919 chi ∧
      Fin15AnchoredAtom3944 chi ∧
      Fin15AnchoredAtom3979 chi ∧
      Fin15AnchoredAtom4715 chi))) ∨
      (((Fin15AnchoredAtom3912 chi ∧
      Fin15AnchoredAtom3916 chi ∧
      Fin15AnchoredAtom3920 chi ∧
      Fin15AnchoredAtom3945 chi ∧
      Fin15AnchoredAtom3980 chi ∧
      Fin15AnchoredAtom4716 chi) ∨
      (Fin15AnchoredAtom3913 chi ∧
      Fin15AnchoredAtom3914 chi ∧
      Fin15AnchoredAtom3921 chi ∧
      Fin15AnchoredAtom3946 chi ∧
      Fin15AnchoredAtom3981 chi ∧
      Fin15AnchoredAtom4717 chi)) ∨
      ((Fin15AnchoredAtom3914 chi ∧
      Fin15AnchoredAtom3915 chi ∧
      Fin15AnchoredAtom3924 chi ∧
      Fin15AnchoredAtom3949 chi ∧
      Fin15AnchoredAtom3984 chi ∧
      Fin15AnchoredAtom4720 chi) ∨
      (Fin15AnchoredAtom3914 chi ∧
      Fin15AnchoredAtom3916 chi ∧
      Fin15AnchoredAtom3925 chi ∧
      Fin15AnchoredAtom3950 chi ∧
      Fin15AnchoredAtom3985 chi ∧
      Fin15AnchoredAtom4721 chi)))))) ∨
      ((((((Fin15AnchoredAtom3915 chi ∧
      Fin15AnchoredAtom3916 chi ∧
      Fin15AnchoredAtom3926 chi ∧
      Fin15AnchoredAtom3951 chi ∧
      Fin15AnchoredAtom3986 chi ∧
      Fin15AnchoredAtom4722 chi) ∨
      (Fin15AnchoredAtom3917 chi ∧
      Fin15AnchoredAtom3919 chi ∧
      Fin15AnchoredAtom3922 chi ∧
      Fin15AnchoredAtom3953 chi ∧
      Fin15AnchoredAtom3988 chi ∧
      Fin15AnchoredAtom4724 chi)) ∨
      ((Fin15AnchoredAtom3918 chi ∧
      Fin15AnchoredAtom3919 chi ∧
      Fin15AnchoredAtom3924 chi ∧
      Fin15AnchoredAtom3955 chi ∧
      Fin15AnchoredAtom3990 chi ∧
      Fin15AnchoredAtom4726 chi) ∨
      (Fin15AnchoredAtom3918 chi ∧
      Fin15AnchoredAtom3920 chi ∧
      Fin15AnchoredAtom3925 chi ∧
      Fin15AnchoredAtom3956 chi ∧
      Fin15AnchoredAtom3991 chi ∧
      Fin15AnchoredAtom4727 chi))) ∨
      (((Fin15AnchoredAtom3919 chi ∧
      Fin15AnchoredAtom3920 chi ∧
      Fin15AnchoredAtom3926 chi ∧
      Fin15AnchoredAtom3957 chi ∧
      Fin15AnchoredAtom3992 chi ∧
      Fin15AnchoredAtom4728 chi) ∨
      (Fin15AnchoredAtom3924 chi ∧
      Fin15AnchoredAtom3925 chi ∧
      Fin15AnchoredAtom3926 chi ∧
      Fin15AnchoredAtom3961 chi ∧
      Fin15AnchoredAtom3996 chi ∧
      Fin15AnchoredAtom4732 chi)) ∨
      ((Fin15AnchoredAtom3942 chi ∧
      Fin15AnchoredAtom3943 chi ∧
      Fin15AnchoredAtom3946 chi ∧
      Fin15AnchoredAtom3952 chi ∧
      Fin15AnchoredAtom4017 chi ∧
      Fin15AnchoredAtom4753 chi) ∨
      (Fin15AnchoredAtom3943 chi ∧
      Fin15AnchoredAtom3944 chi ∧
      Fin15AnchoredAtom3949 chi ∧
      Fin15AnchoredAtom3955 chi ∧
      Fin15AnchoredAtom4020 chi ∧
      Fin15AnchoredAtom4756 chi)))) ∨
      ((((Fin15AnchoredAtom3943 chi ∧
      Fin15AnchoredAtom3945 chi ∧
      Fin15AnchoredAtom3950 chi ∧
      Fin15AnchoredAtom3956 chi ∧
      Fin15AnchoredAtom4021 chi ∧
      Fin15AnchoredAtom4757 chi) ∨
      (Fin15AnchoredAtom3944 chi ∧
      Fin15AnchoredAtom3945 chi ∧
      Fin15AnchoredAtom3951 chi ∧
      Fin15AnchoredAtom3957 chi ∧
      Fin15AnchoredAtom4022 chi ∧
      Fin15AnchoredAtom4758 chi)) ∨
      ((Fin15AnchoredAtom3946 chi ∧
      Fin15AnchoredAtom3947 chi ∧
      Fin15AnchoredAtom3949 chi ∧
      Fin15AnchoredAtom3958 chi ∧
      Fin15AnchoredAtom4023 chi ∧
      Fin15AnchoredAtom4759 chi) ∨
      (Fin15AnchoredAtom3949 chi ∧
      Fin15AnchoredAtom3950 chi ∧
      Fin15AnchoredAtom3951 chi ∧
      Fin15AnchoredAtom3961 chi ∧
      Fin15AnchoredAtom4026 chi ∧
      Fin15AnchoredAtom4762 chi))) ∨
      (((Fin15AnchoredAtom3952 chi ∧
      Fin15AnchoredAtom3953 chi ∧
      Fin15AnchoredAtom3955 chi ∧
      Fin15AnchoredAtom3958 chi ∧
      Fin15AnchoredAtom4027 chi ∧
      Fin15AnchoredAtom4763 chi) ∨
      (Fin15AnchoredAtom3955 chi ∧
      Fin15AnchoredAtom3956 chi ∧
      Fin15AnchoredAtom3957 chi ∧
      Fin15AnchoredAtom3961 chi ∧
      Fin15AnchoredAtom4030 chi ∧
      Fin15AnchoredAtom4766 chi)) ∨
      ((Fin15AnchoredAtom3977 chi ∧
      Fin15AnchoredAtom3978 chi ∧
      Fin15AnchoredAtom3981 chi ∧
      Fin15AnchoredAtom3987 chi ∧
      Fin15AnchoredAtom4017 chi ∧
      Fin15AnchoredAtom4788 chi) ∨
      (Fin15AnchoredAtom3978 chi ∧
      Fin15AnchoredAtom3979 chi ∧
      Fin15AnchoredAtom3984 chi ∧
      Fin15AnchoredAtom3990 chi ∧
      Fin15AnchoredAtom4020 chi ∧
      Fin15AnchoredAtom4791 chi))))) ∨
      (((((Fin15AnchoredAtom3978 chi ∧
      Fin15AnchoredAtom3980 chi ∧
      Fin15AnchoredAtom3985 chi ∧
      Fin15AnchoredAtom3991 chi ∧
      Fin15AnchoredAtom4021 chi ∧
      Fin15AnchoredAtom4792 chi) ∨
      (Fin15AnchoredAtom3979 chi ∧
      Fin15AnchoredAtom3980 chi ∧
      Fin15AnchoredAtom3986 chi ∧
      Fin15AnchoredAtom3992 chi ∧
      Fin15AnchoredAtom4022 chi ∧
      Fin15AnchoredAtom4793 chi)) ∨
      ((Fin15AnchoredAtom3984 chi ∧
      Fin15AnchoredAtom3985 chi ∧
      Fin15AnchoredAtom3986 chi ∧
      Fin15AnchoredAtom3996 chi ∧
      Fin15AnchoredAtom4026 chi ∧
      Fin15AnchoredAtom4797 chi) ∨
      (Fin15AnchoredAtom3988 chi ∧
      Fin15AnchoredAtom3989 chi ∧
      Fin15AnchoredAtom3992 chi ∧
      Fin15AnchoredAtom3995 chi ∧
      Fin15AnchoredAtom4029 chi ∧
      Fin15AnchoredAtom4800 chi))) ∨
      (((Fin15AnchoredAtom3990 chi ∧
      Fin15AnchoredAtom3991 chi ∧
      Fin15AnchoredAtom3992 chi ∧
      Fin15AnchoredAtom3996 chi ∧
      Fin15AnchoredAtom4030 chi ∧
      Fin15AnchoredAtom4801 chi) ∨
      (Fin15AnchoredAtom4020 chi ∧
      Fin15AnchoredAtom4021 chi ∧
      Fin15AnchoredAtom4022 chi ∧
      Fin15AnchoredAtom4026 chi ∧
      Fin15AnchoredAtom4030 chi ∧
      Fin15AnchoredAtom4821 chi)) ∨
      ((Fin15AnchoredAtom4032 chi ∧
      Fin15AnchoredAtom4033 chi ∧
      Fin15AnchoredAtom4040 chi ∧
      Fin15AnchoredAtom4068 chi ∧
      Fin15AnchoredAtom4152 chi ∧
      Fin15AnchoredAtom4362 chi) ∨
      (Fin15AnchoredAtom4032 chi ∧
      Fin15AnchoredAtom4034 chi ∧
      Fin15AnchoredAtom4041 chi ∧
      Fin15AnchoredAtom4069 chi ∧
      Fin15AnchoredAtom4153 chi ∧
      Fin15AnchoredAtom4363 chi)))) ∨
      ((((Fin15AnchoredAtom4032 chi ∧
      Fin15AnchoredAtom4035 chi ∧
      Fin15AnchoredAtom4042 chi ∧
      Fin15AnchoredAtom4070 chi ∧
      Fin15AnchoredAtom4154 chi ∧
      Fin15AnchoredAtom4364 chi) ∨
      (Fin15AnchoredAtom4032 chi ∧
      Fin15AnchoredAtom4037 chi ∧
      Fin15AnchoredAtom4044 chi ∧
      Fin15AnchoredAtom4072 chi ∧
      Fin15AnchoredAtom4156 chi ∧
      Fin15AnchoredAtom4366 chi)) ∨
      ((Fin15AnchoredAtom4032 chi ∧
      Fin15AnchoredAtom4038 chi ∧
      Fin15AnchoredAtom4045 chi ∧
      Fin15AnchoredAtom4073 chi ∧
      Fin15AnchoredAtom4157 chi ∧
      Fin15AnchoredAtom4367 chi) ∨
      (Fin15AnchoredAtom4032 chi ∧
      Fin15AnchoredAtom4039 chi ∧
      Fin15AnchoredAtom4046 chi ∧
      Fin15AnchoredAtom4074 chi ∧
      Fin15AnchoredAtom4158 chi ∧
      Fin15AnchoredAtom4368 chi))) ∨
      (((Fin15AnchoredAtom4033 chi ∧
      Fin15AnchoredAtom4034 chi ∧
      Fin15AnchoredAtom4047 chi ∧
      Fin15AnchoredAtom4075 chi ∧
      Fin15AnchoredAtom4159 chi ∧
      Fin15AnchoredAtom4369 chi) ∨
      (Fin15AnchoredAtom4033 chi ∧
      Fin15AnchoredAtom4035 chi ∧
      Fin15AnchoredAtom4048 chi ∧
      Fin15AnchoredAtom4076 chi ∧
      Fin15AnchoredAtom4160 chi ∧
      Fin15AnchoredAtom4370 chi)) ∨
      ((Fin15AnchoredAtom4033 chi ∧
      Fin15AnchoredAtom4037 chi ∧
      Fin15AnchoredAtom4050 chi ∧
      Fin15AnchoredAtom4078 chi ∧
      Fin15AnchoredAtom4162 chi ∧
      Fin15AnchoredAtom4372 chi) ∨
      (Fin15AnchoredAtom4034 chi ∧
      Fin15AnchoredAtom4035 chi ∧
      Fin15AnchoredAtom4053 chi ∧
      Fin15AnchoredAtom4081 chi ∧
      Fin15AnchoredAtom4165 chi ∧
      Fin15AnchoredAtom4375 chi)))))))) ∨
      (((((((Fin15AnchoredAtom4034 chi ∧
      Fin15AnchoredAtom4037 chi ∧
      Fin15AnchoredAtom4055 chi ∧
      Fin15AnchoredAtom4083 chi ∧
      Fin15AnchoredAtom4167 chi ∧
      Fin15AnchoredAtom4377 chi) ∨
      ((Fin15AnchoredAtom4034 chi ∧
      Fin15AnchoredAtom4038 chi ∧
      Fin15AnchoredAtom4056 chi ∧
      Fin15AnchoredAtom4084 chi ∧
      Fin15AnchoredAtom4168 chi ∧
      Fin15AnchoredAtom4378 chi) ∨
      (Fin15AnchoredAtom4034 chi ∧
      Fin15AnchoredAtom4039 chi ∧
      Fin15AnchoredAtom4057 chi ∧
      Fin15AnchoredAtom4085 chi ∧
      Fin15AnchoredAtom4169 chi ∧
      Fin15AnchoredAtom4379 chi))) ∨
      (((Fin15AnchoredAtom4035 chi ∧
      Fin15AnchoredAtom4037 chi ∧
      Fin15AnchoredAtom4059 chi ∧
      Fin15AnchoredAtom4087 chi ∧
      Fin15AnchoredAtom4171 chi ∧
      Fin15AnchoredAtom4381 chi) ∨
      (Fin15AnchoredAtom4035 chi ∧
      Fin15AnchoredAtom4038 chi ∧
      Fin15AnchoredAtom4060 chi ∧
      Fin15AnchoredAtom4088 chi ∧
      Fin15AnchoredAtom4172 chi ∧
      Fin15AnchoredAtom4382 chi)) ∨
      ((Fin15AnchoredAtom4035 chi ∧
      Fin15AnchoredAtom4039 chi ∧
      Fin15AnchoredAtom4061 chi ∧
      Fin15AnchoredAtom4089 chi ∧
      Fin15AnchoredAtom4173 chi ∧
      Fin15AnchoredAtom4383 chi) ∨
      (Fin15AnchoredAtom4037 chi ∧
      Fin15AnchoredAtom4038 chi ∧
      Fin15AnchoredAtom4065 chi ∧
      Fin15AnchoredAtom4093 chi ∧
      Fin15AnchoredAtom4177 chi ∧
      Fin15AnchoredAtom4387 chi)))) ∨
      ((((Fin15AnchoredAtom4037 chi ∧
      Fin15AnchoredAtom4039 chi ∧
      Fin15AnchoredAtom4066 chi ∧
      Fin15AnchoredAtom4094 chi ∧
      Fin15AnchoredAtom4178 chi ∧
      Fin15AnchoredAtom4388 chi) ∨
      (Fin15AnchoredAtom4038 chi ∧
      Fin15AnchoredAtom4039 chi ∧
      Fin15AnchoredAtom4067 chi ∧
      Fin15AnchoredAtom4095 chi ∧
      Fin15AnchoredAtom4179 chi ∧
      Fin15AnchoredAtom4389 chi)) ∨
      ((Fin15AnchoredAtom4040 chi ∧
      Fin15AnchoredAtom4041 chi ∧
      Fin15AnchoredAtom4047 chi ∧
      Fin15AnchoredAtom4096 chi ∧
      Fin15AnchoredAtom4180 chi ∧
      Fin15AnchoredAtom4390 chi) ∨
      (Fin15AnchoredAtom4040 chi ∧
      Fin15AnchoredAtom4042 chi ∧
      Fin15AnchoredAtom4048 chi ∧
      Fin15AnchoredAtom4097 chi ∧
      Fin15AnchoredAtom4181 chi ∧
      Fin15AnchoredAtom4391 chi))) ∨
      (((Fin15AnchoredAtom4040 chi ∧
      Fin15AnchoredAtom4044 chi ∧
      Fin15AnchoredAtom4050 chi ∧
      Fin15AnchoredAtom4099 chi ∧
      Fin15AnchoredAtom4183 chi ∧
      Fin15AnchoredAtom4393 chi) ∨
      (Fin15AnchoredAtom4040 chi ∧
      Fin15AnchoredAtom4045 chi ∧
      Fin15AnchoredAtom4051 chi ∧
      Fin15AnchoredAtom4100 chi ∧
      Fin15AnchoredAtom4184 chi ∧
      Fin15AnchoredAtom4394 chi)) ∨
      ((Fin15AnchoredAtom4040 chi ∧
      Fin15AnchoredAtom4046 chi ∧
      Fin15AnchoredAtom4052 chi ∧
      Fin15AnchoredAtom4101 chi ∧
      Fin15AnchoredAtom4185 chi ∧
      Fin15AnchoredAtom4395 chi) ∨
      (Fin15AnchoredAtom4041 chi ∧
      Fin15AnchoredAtom4042 chi ∧
      Fin15AnchoredAtom4053 chi ∧
      Fin15AnchoredAtom4102 chi ∧
      Fin15AnchoredAtom4186 chi ∧
      Fin15AnchoredAtom4396 chi))))) ∨
      (((((Fin15AnchoredAtom4041 chi ∧
      Fin15AnchoredAtom4044 chi ∧
      Fin15AnchoredAtom4055 chi ∧
      Fin15AnchoredAtom4104 chi ∧
      Fin15AnchoredAtom4188 chi ∧
      Fin15AnchoredAtom4398 chi) ∨
      (Fin15AnchoredAtom4041 chi ∧
      Fin15AnchoredAtom4045 chi ∧
      Fin15AnchoredAtom4056 chi ∧
      Fin15AnchoredAtom4105 chi ∧
      Fin15AnchoredAtom4189 chi ∧
      Fin15AnchoredAtom4399 chi)) ∨
      ((Fin15AnchoredAtom4041 chi ∧
      Fin15AnchoredAtom4046 chi ∧
      Fin15AnchoredAtom4057 chi ∧
      Fin15AnchoredAtom4106 chi ∧
      Fin15AnchoredAtom4190 chi ∧
      Fin15AnchoredAtom4400 chi) ∨
      (Fin15AnchoredAtom4042 chi ∧
      Fin15AnchoredAtom4044 chi ∧
      Fin15AnchoredAtom4059 chi ∧
      Fin15AnchoredAtom4108 chi ∧
      Fin15AnchoredAtom4192 chi ∧
      Fin15AnchoredAtom4402 chi))) ∨
      (((Fin15AnchoredAtom4042 chi ∧
      Fin15AnchoredAtom4045 chi ∧
      Fin15AnchoredAtom4060 chi ∧
      Fin15AnchoredAtom4109 chi ∧
      Fin15AnchoredAtom4193 chi ∧
      Fin15AnchoredAtom4403 chi) ∨
      (Fin15AnchoredAtom4042 chi ∧
      Fin15AnchoredAtom4046 chi ∧
      Fin15AnchoredAtom4061 chi ∧
      Fin15AnchoredAtom4110 chi ∧
      Fin15AnchoredAtom4194 chi ∧
      Fin15AnchoredAtom4404 chi)) ∨
      ((Fin15AnchoredAtom4044 chi ∧
      Fin15AnchoredAtom4045 chi ∧
      Fin15AnchoredAtom4065 chi ∧
      Fin15AnchoredAtom4114 chi ∧
      Fin15AnchoredAtom4198 chi ∧
      Fin15AnchoredAtom4408 chi) ∨
      (Fin15AnchoredAtom4044 chi ∧
      Fin15AnchoredAtom4046 chi ∧
      Fin15AnchoredAtom4066 chi ∧
      Fin15AnchoredAtom4115 chi ∧
      Fin15AnchoredAtom4199 chi ∧
      Fin15AnchoredAtom4409 chi)))) ∨
      ((((Fin15AnchoredAtom4045 chi ∧
      Fin15AnchoredAtom4046 chi ∧
      Fin15AnchoredAtom4067 chi ∧
      Fin15AnchoredAtom4116 chi ∧
      Fin15AnchoredAtom4200 chi ∧
      Fin15AnchoredAtom4410 chi) ∨
      (Fin15AnchoredAtom4047 chi ∧
      Fin15AnchoredAtom4048 chi ∧
      Fin15AnchoredAtom4053 chi ∧
      Fin15AnchoredAtom4117 chi ∧
      Fin15AnchoredAtom4201 chi ∧
      Fin15AnchoredAtom4411 chi)) ∨
      ((Fin15AnchoredAtom4048 chi ∧
      Fin15AnchoredAtom4050 chi ∧
      Fin15AnchoredAtom4059 chi ∧
      Fin15AnchoredAtom4123 chi ∧
      Fin15AnchoredAtom4207 chi ∧
      Fin15AnchoredAtom4417 chi) ∨
      (Fin15AnchoredAtom4048 chi ∧
      Fin15AnchoredAtom4051 chi ∧
      Fin15AnchoredAtom4060 chi ∧
      Fin15AnchoredAtom4124 chi ∧
      Fin15AnchoredAtom4208 chi ∧
      Fin15AnchoredAtom4418 chi))) ∨
      (((Fin15AnchoredAtom4053 chi ∧
      Fin15AnchoredAtom4054 chi ∧
      Fin15AnchoredAtom4058 chi ∧
      Fin15AnchoredAtom4132 chi ∧
      Fin15AnchoredAtom4216 chi ∧
      Fin15AnchoredAtom4426 chi) ∨
      (Fin15AnchoredAtom4053 chi ∧
      Fin15AnchoredAtom4055 chi ∧
      Fin15AnchoredAtom4059 chi ∧
      Fin15AnchoredAtom4133 chi ∧
      Fin15AnchoredAtom4217 chi ∧
      Fin15AnchoredAtom4427 chi)) ∨
      ((Fin15AnchoredAtom4053 chi ∧
      Fin15AnchoredAtom4056 chi ∧
      Fin15AnchoredAtom4060 chi ∧
      Fin15AnchoredAtom4134 chi ∧
      Fin15AnchoredAtom4218 chi ∧
      Fin15AnchoredAtom4428 chi) ∨
      (Fin15AnchoredAtom4053 chi ∧
      Fin15AnchoredAtom4057 chi ∧
      Fin15AnchoredAtom4061 chi ∧
      Fin15AnchoredAtom4135 chi ∧
      Fin15AnchoredAtom4219 chi ∧
      Fin15AnchoredAtom4429 chi)))))) ∨
      ((((((Fin15AnchoredAtom4055 chi ∧
      Fin15AnchoredAtom4056 chi ∧
      Fin15AnchoredAtom4065 chi ∧
      Fin15AnchoredAtom4139 chi ∧
      Fin15AnchoredAtom4223 chi ∧
      Fin15AnchoredAtom4433 chi) ∨
      (Fin15AnchoredAtom4055 chi ∧
      Fin15AnchoredAtom4057 chi ∧
      Fin15AnchoredAtom4066 chi ∧
      Fin15AnchoredAtom4140 chi ∧
      Fin15AnchoredAtom4224 chi ∧
      Fin15AnchoredAtom4434 chi)) ∨
      ((Fin15AnchoredAtom4056 chi ∧
      Fin15AnchoredAtom4057 chi ∧
      Fin15AnchoredAtom4067 chi ∧
      Fin15AnchoredAtom4141 chi ∧
      Fin15AnchoredAtom4225 chi ∧
      Fin15AnchoredAtom4435 chi) ∨
      (Fin15AnchoredAtom4059 chi ∧
      Fin15AnchoredAtom4060 chi ∧
      Fin15AnchoredAtom4065 chi ∧
      Fin15AnchoredAtom4145 chi ∧
      Fin15AnchoredAtom4229 chi ∧
      Fin15AnchoredAtom4439 chi))) ∨
      (((Fin15AnchoredAtom4059 chi ∧
      Fin15AnchoredAtom4061 chi ∧
      Fin15AnchoredAtom4066 chi ∧
      Fin15AnchoredAtom4146 chi ∧
      Fin15AnchoredAtom4230 chi ∧
      Fin15AnchoredAtom4440 chi) ∨
      (Fin15AnchoredAtom4060 chi ∧
      Fin15AnchoredAtom4061 chi ∧
      Fin15AnchoredAtom4067 chi ∧
      Fin15AnchoredAtom4147 chi ∧
      Fin15AnchoredAtom4231 chi ∧
      Fin15AnchoredAtom4441 chi)) ∨
      ((Fin15AnchoredAtom4065 chi ∧
      Fin15AnchoredAtom4066 chi ∧
      Fin15AnchoredAtom4067 chi ∧
      Fin15AnchoredAtom4151 chi ∧
      Fin15AnchoredAtom4235 chi ∧
      Fin15AnchoredAtom4445 chi) ∨
      (Fin15AnchoredAtom4068 chi ∧
      Fin15AnchoredAtom4069 chi ∧
      Fin15AnchoredAtom4075 chi ∧
      Fin15AnchoredAtom4096 chi ∧
      Fin15AnchoredAtom4236 chi ∧
      Fin15AnchoredAtom4446 chi)))) ∨
      ((((Fin15AnchoredAtom4068 chi ∧
      Fin15AnchoredAtom4070 chi ∧
      Fin15AnchoredAtom4076 chi ∧
      Fin15AnchoredAtom4097 chi ∧
      Fin15AnchoredAtom4237 chi ∧
      Fin15AnchoredAtom4447 chi) ∨
      (Fin15AnchoredAtom4068 chi ∧
      Fin15AnchoredAtom4072 chi ∧
      Fin15AnchoredAtom4078 chi ∧
      Fin15AnchoredAtom4099 chi ∧
      Fin15AnchoredAtom4239 chi ∧
      Fin15AnchoredAtom4449 chi)) ∨
      ((Fin15AnchoredAtom4068 chi ∧
      Fin15AnchoredAtom4074 chi ∧
      Fin15AnchoredAtom4080 chi ∧
      Fin15AnchoredAtom4101 chi ∧
      Fin15AnchoredAtom4241 chi ∧
      Fin15AnchoredAtom4451 chi) ∨
      (Fin15AnchoredAtom4069 chi ∧
      Fin15AnchoredAtom4070 chi ∧
      Fin15AnchoredAtom4081 chi ∧
      Fin15AnchoredAtom4102 chi ∧
      Fin15AnchoredAtom4242 chi ∧
      Fin15AnchoredAtom4452 chi))) ∨
      (((Fin15AnchoredAtom4069 chi ∧
      Fin15AnchoredAtom4072 chi ∧
      Fin15AnchoredAtom4083 chi ∧
      Fin15AnchoredAtom4104 chi ∧
      Fin15AnchoredAtom4244 chi ∧
      Fin15AnchoredAtom4454 chi) ∨
      (Fin15AnchoredAtom4069 chi ∧
      Fin15AnchoredAtom4073 chi ∧
      Fin15AnchoredAtom4084 chi ∧
      Fin15AnchoredAtom4105 chi ∧
      Fin15AnchoredAtom4245 chi ∧
      Fin15AnchoredAtom4455 chi)) ∨
      ((Fin15AnchoredAtom4069 chi ∧
      Fin15AnchoredAtom4074 chi ∧
      Fin15AnchoredAtom4085 chi ∧
      Fin15AnchoredAtom4106 chi ∧
      Fin15AnchoredAtom4246 chi ∧
      Fin15AnchoredAtom4456 chi) ∨
      (Fin15AnchoredAtom4070 chi ∧
      Fin15AnchoredAtom4072 chi ∧
      Fin15AnchoredAtom4087 chi ∧
      Fin15AnchoredAtom4108 chi ∧
      Fin15AnchoredAtom4248 chi ∧
      Fin15AnchoredAtom4458 chi))))) ∨
      (((((Fin15AnchoredAtom4070 chi ∧
      Fin15AnchoredAtom4073 chi ∧
      Fin15AnchoredAtom4088 chi ∧
      Fin15AnchoredAtom4109 chi ∧
      Fin15AnchoredAtom4249 chi ∧
      Fin15AnchoredAtom4459 chi) ∨
      (Fin15AnchoredAtom4070 chi ∧
      Fin15AnchoredAtom4074 chi ∧
      Fin15AnchoredAtom4089 chi ∧
      Fin15AnchoredAtom4110 chi ∧
      Fin15AnchoredAtom4250 chi ∧
      Fin15AnchoredAtom4460 chi)) ∨
      ((Fin15AnchoredAtom4072 chi ∧
      Fin15AnchoredAtom4073 chi ∧
      Fin15AnchoredAtom4093 chi ∧
      Fin15AnchoredAtom4114 chi ∧
      Fin15AnchoredAtom4254 chi ∧
      Fin15AnchoredAtom4464 chi) ∨
      (Fin15AnchoredAtom4072 chi ∧
      Fin15AnchoredAtom4074 chi ∧
      Fin15AnchoredAtom4094 chi ∧
      Fin15AnchoredAtom4115 chi ∧
      Fin15AnchoredAtom4255 chi ∧
      Fin15AnchoredAtom4465 chi))) ∨
      (((Fin15AnchoredAtom4073 chi ∧
      Fin15AnchoredAtom4074 chi ∧
      Fin15AnchoredAtom4095 chi ∧
      Fin15AnchoredAtom4116 chi ∧
      Fin15AnchoredAtom4256 chi ∧
      Fin15AnchoredAtom4466 chi) ∨
      (Fin15AnchoredAtom4075 chi ∧
      Fin15AnchoredAtom4076 chi ∧
      Fin15AnchoredAtom4081 chi ∧
      Fin15AnchoredAtom4117 chi ∧
      Fin15AnchoredAtom4257 chi ∧
      Fin15AnchoredAtom4467 chi)) ∨
      ((Fin15AnchoredAtom4075 chi ∧
      Fin15AnchoredAtom4080 chi ∧
      Fin15AnchoredAtom4085 chi ∧
      Fin15AnchoredAtom4121 chi ∧
      Fin15AnchoredAtom4261 chi ∧
      Fin15AnchoredAtom4471 chi) ∨
      (Fin15AnchoredAtom4076 chi ∧
      Fin15AnchoredAtom4079 chi ∧
      Fin15AnchoredAtom4088 chi ∧
      Fin15AnchoredAtom4124 chi ∧
      Fin15AnchoredAtom4264 chi ∧
      Fin15AnchoredAtom4474 chi)))) ∨
      ((((Fin15AnchoredAtom4076 chi ∧
      Fin15AnchoredAtom4080 chi ∧
      Fin15AnchoredAtom4089 chi ∧
      Fin15AnchoredAtom4125 chi ∧
      Fin15AnchoredAtom4265 chi ∧
      Fin15AnchoredAtom4475 chi) ∨
      (Fin15AnchoredAtom4078 chi ∧
      Fin15AnchoredAtom4080 chi ∧
      Fin15AnchoredAtom4094 chi ∧
      Fin15AnchoredAtom4130 chi ∧
      Fin15AnchoredAtom4270 chi ∧
      Fin15AnchoredAtom4480 chi)) ∨
      ((Fin15AnchoredAtom4081 chi ∧
      Fin15AnchoredAtom4082 chi ∧
      Fin15AnchoredAtom4086 chi ∧
      Fin15AnchoredAtom4132 chi ∧
      Fin15AnchoredAtom4272 chi ∧
      Fin15AnchoredAtom4482 chi) ∨
      (Fin15AnchoredAtom4081 chi ∧
      Fin15AnchoredAtom4083 chi ∧
      Fin15AnchoredAtom4087 chi ∧
      Fin15AnchoredAtom4133 chi ∧
      Fin15AnchoredAtom4273 chi ∧
      Fin15AnchoredAtom4483 chi))) ∨
      (((Fin15AnchoredAtom4081 chi ∧
      Fin15AnchoredAtom4084 chi ∧
      Fin15AnchoredAtom4088 chi ∧
      Fin15AnchoredAtom4134 chi ∧
      Fin15AnchoredAtom4274 chi ∧
      Fin15AnchoredAtom4484 chi) ∨
      (Fin15AnchoredAtom4081 chi ∧
      Fin15AnchoredAtom4085 chi ∧
      Fin15AnchoredAtom4089 chi ∧
      Fin15AnchoredAtom4135 chi ∧
      Fin15AnchoredAtom4275 chi ∧
      Fin15AnchoredAtom4485 chi)) ∨
      ((Fin15AnchoredAtom4083 chi ∧
      Fin15AnchoredAtom4084 chi ∧
      Fin15AnchoredAtom4093 chi ∧
      Fin15AnchoredAtom4139 chi ∧
      Fin15AnchoredAtom4279 chi ∧
      Fin15AnchoredAtom4489 chi) ∨
      (Fin15AnchoredAtom4083 chi ∧
      Fin15AnchoredAtom4085 chi ∧
      Fin15AnchoredAtom4094 chi ∧
      Fin15AnchoredAtom4140 chi ∧
      Fin15AnchoredAtom4280 chi ∧
      Fin15AnchoredAtom4490 chi))))))) ∨
      (((((((Fin15AnchoredAtom4084 chi ∧
      Fin15AnchoredAtom4085 chi ∧
      Fin15AnchoredAtom4095 chi ∧
      Fin15AnchoredAtom4141 chi ∧
      Fin15AnchoredAtom4281 chi ∧
      Fin15AnchoredAtom4491 chi) ∨
      (Fin15AnchoredAtom4087 chi ∧
      Fin15AnchoredAtom4088 chi ∧
      Fin15AnchoredAtom4093 chi ∧
      Fin15AnchoredAtom4145 chi ∧
      Fin15AnchoredAtom4285 chi ∧
      Fin15AnchoredAtom4495 chi)) ∨
      ((Fin15AnchoredAtom4087 chi ∧
      Fin15AnchoredAtom4089 chi ∧
      Fin15AnchoredAtom4094 chi ∧
      Fin15AnchoredAtom4146 chi ∧
      Fin15AnchoredAtom4286 chi ∧
      Fin15AnchoredAtom4496 chi) ∨
      (Fin15AnchoredAtom4088 chi ∧
      Fin15AnchoredAtom4089 chi ∧
      Fin15AnchoredAtom4095 chi ∧
      Fin15AnchoredAtom4147 chi ∧
      Fin15AnchoredAtom4287 chi ∧
      Fin15AnchoredAtom4497 chi))) ∨
      (((Fin15AnchoredAtom4093 chi ∧
      Fin15AnchoredAtom4094 chi ∧
      Fin15AnchoredAtom4095 chi ∧
      Fin15AnchoredAtom4151 chi ∧
      Fin15AnchoredAtom4291 chi ∧
      Fin15AnchoredAtom4501 chi) ∨
      (Fin15AnchoredAtom4096 chi ∧
      Fin15AnchoredAtom4097 chi ∧
      Fin15AnchoredAtom4102 chi ∧
      Fin15AnchoredAtom4117 chi ∧
      Fin15AnchoredAtom4292 chi ∧
      Fin15AnchoredAtom4502 chi)) ∨
      ((Fin15AnchoredAtom4097 chi ∧
      Fin15AnchoredAtom4100 chi ∧
      Fin15AnchoredAtom4109 chi ∧
      Fin15AnchoredAtom4124 chi ∧
      Fin15AnchoredAtom4299 chi ∧
      Fin15AnchoredAtom4509 chi) ∨
      (Fin15AnchoredAtom4099 chi ∧
      Fin15AnchoredAtom4100 chi ∧
      Fin15AnchoredAtom4114 chi ∧
      Fin15AnchoredAtom4129 chi ∧
      Fin15AnchoredAtom4304 chi ∧
      Fin15AnchoredAtom4514 chi)))) ∨
      ((((Fin15AnchoredAtom4099 chi ∧
      Fin15AnchoredAtom4101 chi ∧
      Fin15AnchoredAtom4115 chi ∧
      Fin15AnchoredAtom4130 chi ∧
      Fin15AnchoredAtom4305 chi ∧
      Fin15AnchoredAtom4515 chi) ∨
      (Fin15AnchoredAtom4100 chi ∧
      Fin15AnchoredAtom4101 chi ∧
      Fin15AnchoredAtom4116 chi ∧
      Fin15AnchoredAtom4131 chi ∧
      Fin15AnchoredAtom4306 chi ∧
      Fin15AnchoredAtom4516 chi)) ∨
      ((Fin15AnchoredAtom4102 chi ∧
      Fin15AnchoredAtom4104 chi ∧
      Fin15AnchoredAtom4108 chi ∧
      Fin15AnchoredAtom4133 chi ∧
      Fin15AnchoredAtom4308 chi ∧
      Fin15AnchoredAtom4518 chi) ∨
      (Fin15AnchoredAtom4102 chi ∧
      Fin15AnchoredAtom4105 chi ∧
      Fin15AnchoredAtom4109 chi ∧
      Fin15AnchoredAtom4134 chi ∧
      Fin15AnchoredAtom4309 chi ∧
      Fin15AnchoredAtom4519 chi))) ∨
      (((Fin15AnchoredAtom4102 chi ∧
      Fin15AnchoredAtom4106 chi ∧
      Fin15AnchoredAtom4110 chi ∧
      Fin15AnchoredAtom4135 chi ∧
      Fin15AnchoredAtom4310 chi ∧
      Fin15AnchoredAtom4520 chi) ∨
      (Fin15AnchoredAtom4104 chi ∧
      Fin15AnchoredAtom4105 chi ∧
      Fin15AnchoredAtom4114 chi ∧
      Fin15AnchoredAtom4139 chi ∧
      Fin15AnchoredAtom4314 chi ∧
      Fin15AnchoredAtom4524 chi)) ∨
      ((Fin15AnchoredAtom4104 chi ∧
      Fin15AnchoredAtom4106 chi ∧
      Fin15AnchoredAtom4115 chi ∧
      Fin15AnchoredAtom4140 chi ∧
      Fin15AnchoredAtom4315 chi ∧
      Fin15AnchoredAtom4525 chi) ∨
      (Fin15AnchoredAtom4105 chi ∧
      Fin15AnchoredAtom4106 chi ∧
      Fin15AnchoredAtom4116 chi ∧
      Fin15AnchoredAtom4141 chi ∧
      Fin15AnchoredAtom4316 chi ∧
      Fin15AnchoredAtom4526 chi))))) ∨
      (((((Fin15AnchoredAtom4108 chi ∧
      Fin15AnchoredAtom4109 chi ∧
      Fin15AnchoredAtom4114 chi ∧
      Fin15AnchoredAtom4145 chi ∧
      Fin15AnchoredAtom4320 chi ∧
      Fin15AnchoredAtom4530 chi) ∨
      (Fin15AnchoredAtom4108 chi ∧
      Fin15AnchoredAtom4110 chi ∧
      Fin15AnchoredAtom4115 chi ∧
      Fin15AnchoredAtom4146 chi ∧
      Fin15AnchoredAtom4321 chi ∧
      Fin15AnchoredAtom4531 chi)) ∨
      ((Fin15AnchoredAtom4109 chi ∧
      Fin15AnchoredAtom4110 chi ∧
      Fin15AnchoredAtom4116 chi ∧
      Fin15AnchoredAtom4147 chi ∧
      Fin15AnchoredAtom4322 chi ∧
      Fin15AnchoredAtom4532 chi) ∨
      (Fin15AnchoredAtom4114 chi ∧
      Fin15AnchoredAtom4115 chi ∧
      Fin15AnchoredAtom4116 chi ∧
      Fin15AnchoredAtom4151 chi ∧
      Fin15AnchoredAtom4326 chi ∧
      Fin15AnchoredAtom4536 chi))) ∨
      (((Fin15AnchoredAtom4117 chi ∧
      Fin15AnchoredAtom4120 chi ∧
      Fin15AnchoredAtom4124 chi ∧
      Fin15AnchoredAtom4134 chi ∧
      Fin15AnchoredAtom4329 chi ∧
      Fin15AnchoredAtom4539 chi) ∨
      (Fin15AnchoredAtom4123 chi ∧
      Fin15AnchoredAtom4124 chi ∧
      Fin15AnchoredAtom4129 chi ∧
      Fin15AnchoredAtom4145 chi ∧
      Fin15AnchoredAtom4340 chi ∧
      Fin15AnchoredAtom4550 chi)) ∨
      ((Fin15AnchoredAtom4123 chi ∧
      Fin15AnchoredAtom4125 chi ∧
      Fin15AnchoredAtom4130 chi ∧
      Fin15AnchoredAtom4146 chi ∧
      Fin15AnchoredAtom4341 chi ∧
      Fin15AnchoredAtom4551 chi) ∨
      (Fin15AnchoredAtom4124 chi ∧
      Fin15AnchoredAtom4125 chi ∧
      Fin15AnchoredAtom4131 chi ∧
      Fin15AnchoredAtom4147 chi ∧
      Fin15AnchoredAtom4342 chi ∧
      Fin15AnchoredAtom4552 chi)))) ∨
      ((((Fin15AnchoredAtom4133 chi ∧
      Fin15AnchoredAtom4134 chi ∧
      Fin15AnchoredAtom4139 chi ∧
      Fin15AnchoredAtom4145 chi ∧
      Fin15AnchoredAtom4350 chi ∧
      Fin15AnchoredAtom4560 chi) ∨
      (Fin15AnchoredAtom4133 chi ∧
      Fin15AnchoredAtom4135 chi ∧
      Fin15AnchoredAtom4140 chi ∧
      Fin15AnchoredAtom4146 chi ∧
      Fin15AnchoredAtom4351 chi ∧
      Fin15AnchoredAtom4561 chi)) ∨
      ((Fin15AnchoredAtom4134 chi ∧
      Fin15AnchoredAtom4135 chi ∧
      Fin15AnchoredAtom4141 chi ∧
      Fin15AnchoredAtom4147 chi ∧
      Fin15AnchoredAtom4352 chi ∧
      Fin15AnchoredAtom4562 chi) ∨
      (Fin15AnchoredAtom4139 chi ∧
      Fin15AnchoredAtom4140 chi ∧
      Fin15AnchoredAtom4141 chi ∧
      Fin15AnchoredAtom4151 chi ∧
      Fin15AnchoredAtom4356 chi ∧
      Fin15AnchoredAtom4566 chi))) ∨
      (((Fin15AnchoredAtom4145 chi ∧
      Fin15AnchoredAtom4146 chi ∧
      Fin15AnchoredAtom4147 chi ∧
      Fin15AnchoredAtom4151 chi ∧
      Fin15AnchoredAtom4360 chi ∧
      Fin15AnchoredAtom4570 chi) ∨
      (Fin15AnchoredAtom4153 chi ∧
      Fin15AnchoredAtom4154 chi ∧
      Fin15AnchoredAtom4165 chi ∧
      Fin15AnchoredAtom4186 chi ∧
      Fin15AnchoredAtom4242 chi ∧
      Fin15AnchoredAtom4578 chi)) ∨
      ((Fin15AnchoredAtom4153 chi ∧
      Fin15AnchoredAtom4156 chi ∧
      Fin15AnchoredAtom4167 chi ∧
      Fin15AnchoredAtom4188 chi ∧
      Fin15AnchoredAtom4244 chi ∧
      Fin15AnchoredAtom4580 chi) ∨
      (Fin15AnchoredAtom4153 chi ∧
      Fin15AnchoredAtom4157 chi ∧
      Fin15AnchoredAtom4168 chi ∧
      Fin15AnchoredAtom4189 chi ∧
      Fin15AnchoredAtom4245 chi ∧
      Fin15AnchoredAtom4581 chi)))))) ∨
      ((((((Fin15AnchoredAtom4153 chi ∧
      Fin15AnchoredAtom4158 chi ∧
      Fin15AnchoredAtom4169 chi ∧
      Fin15AnchoredAtom4190 chi ∧
      Fin15AnchoredAtom4246 chi ∧
      Fin15AnchoredAtom4582 chi) ∨
      (Fin15AnchoredAtom4154 chi ∧
      Fin15AnchoredAtom4155 chi ∧
      Fin15AnchoredAtom4170 chi ∧
      Fin15AnchoredAtom4191 chi ∧
      Fin15AnchoredAtom4247 chi ∧
      Fin15AnchoredAtom4583 chi)) ∨
      ((Fin15AnchoredAtom4154 chi ∧
      Fin15AnchoredAtom4156 chi ∧
      Fin15AnchoredAtom4171 chi ∧
      Fin15AnchoredAtom4192 chi ∧
      Fin15AnchoredAtom4248 chi ∧
      Fin15AnchoredAtom4584 chi) ∨
      (Fin15AnchoredAtom4154 chi ∧
      Fin15AnchoredAtom4157 chi ∧
      Fin15AnchoredAtom4172 chi ∧
      Fin15AnchoredAtom4193 chi ∧
      Fin15AnchoredAtom4249 chi ∧
      Fin15AnchoredAtom4585 chi))) ∨
      (((Fin15AnchoredAtom4154 chi ∧
      Fin15AnchoredAtom4158 chi ∧
      Fin15AnchoredAtom4173 chi ∧
      Fin15AnchoredAtom4194 chi ∧
      Fin15AnchoredAtom4250 chi ∧
      Fin15AnchoredAtom4586 chi) ∨
      (Fin15AnchoredAtom4156 chi ∧
      Fin15AnchoredAtom4157 chi ∧
      Fin15AnchoredAtom4177 chi ∧
      Fin15AnchoredAtom4198 chi ∧
      Fin15AnchoredAtom4254 chi ∧
      Fin15AnchoredAtom4590 chi)) ∨
      ((Fin15AnchoredAtom4156 chi ∧
      Fin15AnchoredAtom4158 chi ∧
      Fin15AnchoredAtom4178 chi ∧
      Fin15AnchoredAtom4199 chi ∧
      Fin15AnchoredAtom4255 chi ∧
      Fin15AnchoredAtom4591 chi) ∨
      (Fin15AnchoredAtom4157 chi ∧
      Fin15AnchoredAtom4158 chi ∧
      Fin15AnchoredAtom4179 chi ∧
      Fin15AnchoredAtom4200 chi ∧
      Fin15AnchoredAtom4256 chi ∧
      Fin15AnchoredAtom4592 chi)))) ∨
      ((((Fin15AnchoredAtom4160 chi ∧
      Fin15AnchoredAtom4163 chi ∧
      Fin15AnchoredAtom4172 chi ∧
      Fin15AnchoredAtom4208 chi ∧
      Fin15AnchoredAtom4264 chi ∧
      Fin15AnchoredAtom4600 chi) ∨
      (Fin15AnchoredAtom4165 chi ∧
      Fin15AnchoredAtom4167 chi ∧
      Fin15AnchoredAtom4171 chi ∧
      Fin15AnchoredAtom4217 chi ∧
      Fin15AnchoredAtom4273 chi ∧
      Fin15AnchoredAtom4609 chi)) ∨
      ((Fin15AnchoredAtom4165 chi ∧
      Fin15AnchoredAtom4168 chi ∧
      Fin15AnchoredAtom4172 chi ∧
      Fin15AnchoredAtom4218 chi ∧
      Fin15AnchoredAtom4274 chi ∧
      Fin15AnchoredAtom4610 chi) ∨
      (Fin15AnchoredAtom4165 chi ∧
      Fin15AnchoredAtom4169 chi ∧
      Fin15AnchoredAtom4173 chi ∧
      Fin15AnchoredAtom4219 chi ∧
      Fin15AnchoredAtom4275 chi ∧
      Fin15AnchoredAtom4611 chi))) ∨
      (((Fin15AnchoredAtom4167 chi ∧
      Fin15AnchoredAtom4168 chi ∧
      Fin15AnchoredAtom4177 chi ∧
      Fin15AnchoredAtom4223 chi ∧
      Fin15AnchoredAtom4279 chi ∧
      Fin15AnchoredAtom4615 chi) ∨
      (Fin15AnchoredAtom4167 chi ∧
      Fin15AnchoredAtom4169 chi ∧
      Fin15AnchoredAtom4178 chi ∧
      Fin15AnchoredAtom4224 chi ∧
      Fin15AnchoredAtom4280 chi ∧
      Fin15AnchoredAtom4616 chi)) ∨
      ((Fin15AnchoredAtom4168 chi ∧
      Fin15AnchoredAtom4169 chi ∧
      Fin15AnchoredAtom4179 chi ∧
      Fin15AnchoredAtom4225 chi ∧
      Fin15AnchoredAtom4281 chi ∧
      Fin15AnchoredAtom4617 chi) ∨
      (Fin15AnchoredAtom4171 chi ∧
      Fin15AnchoredAtom4172 chi ∧
      Fin15AnchoredAtom4177 chi ∧
      Fin15AnchoredAtom4229 chi ∧
      Fin15AnchoredAtom4285 chi ∧
      Fin15AnchoredAtom4621 chi))))) ∨
      (((((Fin15AnchoredAtom4171 chi ∧
      Fin15AnchoredAtom4173 chi ∧
      Fin15AnchoredAtom4178 chi ∧
      Fin15AnchoredAtom4230 chi ∧
      Fin15AnchoredAtom4286 chi ∧
      Fin15AnchoredAtom4622 chi) ∨
      (Fin15AnchoredAtom4172 chi ∧
      Fin15AnchoredAtom4173 chi ∧
      Fin15AnchoredAtom4179 chi ∧
      Fin15AnchoredAtom4231 chi ∧
      Fin15AnchoredAtom4287 chi ∧
      Fin15AnchoredAtom4623 chi)) ∨
      ((Fin15AnchoredAtom4177 chi ∧
      Fin15AnchoredAtom4178 chi ∧
      Fin15AnchoredAtom4179 chi ∧
      Fin15AnchoredAtom4235 chi ∧
      Fin15AnchoredAtom4291 chi ∧
      Fin15AnchoredAtom4627 chi) ∨
      (Fin15AnchoredAtom4180 chi ∧
      Fin15AnchoredAtom4181 chi ∧
      Fin15AnchoredAtom4186 chi ∧
      Fin15AnchoredAtom4201 chi ∧
      Fin15AnchoredAtom4292 chi ∧
      Fin15AnchoredAtom4628 chi))) ∨
      (((Fin15AnchoredAtom4181 chi ∧
      Fin15AnchoredAtom4184 chi ∧
      Fin15AnchoredAtom4193 chi ∧
      Fin15AnchoredAtom4208 chi ∧
      Fin15AnchoredAtom4299 chi ∧
      Fin15AnchoredAtom4635 chi) ∨
      (Fin15AnchoredAtom4183 chi ∧
      Fin15AnchoredAtom4184 chi ∧
      Fin15AnchoredAtom4198 chi ∧
      Fin15AnchoredAtom4213 chi ∧
      Fin15AnchoredAtom4304 chi ∧
      Fin15AnchoredAtom4640 chi)) ∨
      ((Fin15AnchoredAtom4186 chi ∧
      Fin15AnchoredAtom4188 chi ∧
      Fin15AnchoredAtom4192 chi ∧
      Fin15AnchoredAtom4217 chi ∧
      Fin15AnchoredAtom4308 chi ∧
      Fin15AnchoredAtom4644 chi) ∨
      (Fin15AnchoredAtom4186 chi ∧
      Fin15AnchoredAtom4189 chi ∧
      Fin15AnchoredAtom4193 chi ∧
      Fin15AnchoredAtom4218 chi ∧
      Fin15AnchoredAtom4309 chi ∧
      Fin15AnchoredAtom4645 chi)))) ∨
      ((((Fin15AnchoredAtom4186 chi ∧
      Fin15AnchoredAtom4190 chi ∧
      Fin15AnchoredAtom4194 chi ∧
      Fin15AnchoredAtom4219 chi ∧
      Fin15AnchoredAtom4310 chi ∧
      Fin15AnchoredAtom4646 chi) ∨
      (Fin15AnchoredAtom4188 chi ∧
      Fin15AnchoredAtom4189 chi ∧
      Fin15AnchoredAtom4198 chi ∧
      Fin15AnchoredAtom4223 chi ∧
      Fin15AnchoredAtom4314 chi ∧
      Fin15AnchoredAtom4650 chi)) ∨
      ((Fin15AnchoredAtom4188 chi ∧
      Fin15AnchoredAtom4190 chi ∧
      Fin15AnchoredAtom4199 chi ∧
      Fin15AnchoredAtom4224 chi ∧
      Fin15AnchoredAtom4315 chi ∧
      Fin15AnchoredAtom4651 chi) ∨
      (Fin15AnchoredAtom4189 chi ∧
      Fin15AnchoredAtom4190 chi ∧
      Fin15AnchoredAtom4200 chi ∧
      Fin15AnchoredAtom4225 chi ∧
      Fin15AnchoredAtom4316 chi ∧
      Fin15AnchoredAtom4652 chi))) ∨
      (((Fin15AnchoredAtom4192 chi ∧
      Fin15AnchoredAtom4193 chi ∧
      Fin15AnchoredAtom4198 chi ∧
      Fin15AnchoredAtom4229 chi ∧
      Fin15AnchoredAtom4320 chi ∧
      Fin15AnchoredAtom4656 chi) ∨
      (Fin15AnchoredAtom4192 chi ∧
      Fin15AnchoredAtom4194 chi ∧
      Fin15AnchoredAtom4199 chi ∧
      Fin15AnchoredAtom4230 chi ∧
      Fin15AnchoredAtom4321 chi ∧
      Fin15AnchoredAtom4657 chi)) ∨
      ((Fin15AnchoredAtom4193 chi ∧
      Fin15AnchoredAtom4194 chi ∧
      Fin15AnchoredAtom4200 chi ∧
      Fin15AnchoredAtom4231 chi ∧
      Fin15AnchoredAtom4322 chi ∧
      Fin15AnchoredAtom4658 chi) ∨
      (Fin15AnchoredAtom4198 chi ∧
      Fin15AnchoredAtom4199 chi ∧
      Fin15AnchoredAtom4200 chi ∧
      Fin15AnchoredAtom4235 chi ∧
      Fin15AnchoredAtom4326 chi ∧
      Fin15AnchoredAtom4662 chi)))))))))) := by
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
                exact fin15Anchored_clause30036 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30037 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30038 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30039 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30040 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30041 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30042 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30043 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30044 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30045 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30046 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30047 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30048 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30049 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30050 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30051 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30052 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30053 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30054 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30055 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30056 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30057 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30058 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30059 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30060 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30061 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30062 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30063 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30064 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30065 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30066 chi hnoStrong hbad
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
                  exact fin15Anchored_clause30067 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30068 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30069 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30070 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30071 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30072 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30073 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30074 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30075 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30076 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30077 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30078 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30079 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30080 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30081 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30082 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30083 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30084 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30085 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30086 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30087 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30088 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30089 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30090 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30091 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30092 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30093 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30094 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30095 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30096 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30097 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30098 chi hnoStrong hbad
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
                exact fin15Anchored_clause30099 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30100 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30101 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30102 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30103 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30104 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30105 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30106 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30107 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30108 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30109 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30110 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30111 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30112 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30113 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30114 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30115 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30116 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30117 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30118 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30119 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30120 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30121 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30122 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30123 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30124 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30125 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30126 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30127 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30128 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30129 chi hnoStrong hbad
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
                  exact fin15Anchored_clause30130 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30131 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30132 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30133 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30134 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30135 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30136 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30137 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30138 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30139 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30140 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30141 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30142 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30143 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30144 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30145 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30146 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30147 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30148 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30149 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30150 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30151 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30152 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30153 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30154 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30155 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30156 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30157 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30158 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30159 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30160 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30161 chi hnoStrong hbad
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
                exact fin15Anchored_clause30162 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30163 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30164 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30165 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30166 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30167 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30168 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30169 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30170 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30171 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30172 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30173 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30174 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30175 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30176 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30177 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30178 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30179 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30180 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30181 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30182 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30183 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30184 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30185 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30186 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30187 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30188 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30189 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30190 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30191 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30192 chi hnoStrong hbad
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
                  exact fin15Anchored_clause30193 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30194 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30195 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30196 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30197 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30198 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30199 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30200 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30201 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30202 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30203 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30204 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30205 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30206 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30207 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30208 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30209 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30210 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30211 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30212 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30213 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30214 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30215 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30216 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30217 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30218 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30219 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30220 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30221 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30222 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30223 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30224 chi hnoStrong hbad
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
                  exact fin15Anchored_clause30225 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30226 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30227 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30228 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30229 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30230 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30231 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30232 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30233 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30234 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30235 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30236 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30237 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30238 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30239 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30240 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30241 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30242 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30243 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30244 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30245 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30246 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30247 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30248 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30249 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30250 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30251 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30252 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30253 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30254 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30255 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30256 chi hnoStrong hbad
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
                  exact fin15Anchored_clause30257 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30258 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30259 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30260 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30261 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30262 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30263 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30264 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30265 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30266 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30267 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30268 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30269 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30270 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30271 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30272 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30273 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30274 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30275 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30276 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30277 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30278 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30279 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30280 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30281 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30282 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30283 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30284 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30285 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30286 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause30287 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause30288 chi hnoStrong hbad

end ErdosSzekeres

end
