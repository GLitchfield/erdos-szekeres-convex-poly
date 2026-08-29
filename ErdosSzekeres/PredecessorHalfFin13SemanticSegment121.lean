module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk092
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk093

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 121. -/

theorem predecessorHalfFin13_rejectSemanticSegment121
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0947 chi) ∨
      ((PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0948 chi) ∨
      (PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0745 chi ∧
      PredecessorHalfFin13Atom0749 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0949 chi))) ∨
      ((PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0950 chi) ∨
      ((PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0951 chi) ∨
      (PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0953 chi)))) ∨
      (((PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0955 chi) ∨
      ((PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0957 chi) ∨
      (PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0959 chi))) ∨
      ((PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0749 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0960 chi) ∨
      ((PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0961 chi) ∨
      (PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0964 chi))))) ∨
      ((((PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0967 chi) ∨
      ((PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0968 chi) ∨
      (PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0970 chi))) ∨
      ((PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0971 chi) ∨
      ((PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0760 chi ∧
      PredecessorHalfFin13Atom0767 chi ∧
      PredecessorHalfFin13Atom0777 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0900 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0972 chi) ∨
      (PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0973 chi)))) ∨
      (((PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0975 chi) ∨
      ((PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0977 chi) ∨
      (PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0764 chi ∧
      PredecessorHalfFin13Atom0767 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0978 chi))) ∨
      ((PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0979 chi) ∨
      ((PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0764 chi ∧
      PredecessorHalfFin13Atom0769 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0980 chi) ∨
      (PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0981 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0767 chi ∧
      PredecessorHalfFin13Atom0769 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0983 chi) ∨
      ((PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0984 chi) ∨
      (PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0735 chi ∧
      PredecessorHalfFin13Atom0767 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0771 chi ∧
      PredecessorHalfFin13Atom0790 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0911 chi ∧
      PredecessorHalfFin13Atom0930 chi ∧
      PredecessorHalfFin13Atom0985 chi))) ∨
      ((PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0987 chi) ∨
      ((PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0777 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0988 chi) ∨
      (PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0989 chi)))) ∨
      (((PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0779 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0919 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0990 chi) ∨
      ((PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0991 chi) ∨
      (PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0994 chi))) ∨
      ((PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0735 chi ∧
      PredecessorHalfFin13Atom0777 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0781 chi ∧
      PredecessorHalfFin13Atom0790 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0921 chi ∧
      PredecessorHalfFin13Atom0930 chi ∧
      PredecessorHalfFin13Atom0995 chi) ∨
      ((PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0997 chi) ∨
      (PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0998 chi))))) ∨
      ((((PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0735 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0787 chi ∧
      PredecessorHalfFin13Atom0790 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0927 chi ∧
      PredecessorHalfFin13Atom0930 chi ∧
      PredecessorHalfFin13Atom0999 chi) ∨
      ((PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0735 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0790 chi ∧
      PredecessorHalfFin13Atom0791 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0930 chi ∧
      PredecessorHalfFin13Atom0931 chi ∧
      PredecessorHalfFin13Atom1001 chi) ∨
      (PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0967 chi))) ∨
      ((PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0968 chi) ∨
      ((PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0932 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0970 chi) ∨
      (PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0971 chi)))) ∨
      (((PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0933 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0973 chi) ∨
      ((PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0740 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0745 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0760 chi ∧
      PredecessorHalfFin13Atom0769 chi ∧
      PredecessorHalfFin13Atom0779 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0935 chi ∧
      PredecessorHalfFin13Atom0944 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0974 chi) ∨
      (PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0934 chi ∧
      PredecessorHalfFin13Atom0936 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0975 chi))) ∨
      (((PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0977 chi) ∨
      (PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0937 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0979 chi)) ∨
      ((PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0938 chi ∧
      PredecessorHalfFin13Atom0940 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0981 chi) ∨
      (PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0941 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0945 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0984 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0740 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0752 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0756 chi ∧
      PredecessorHalfFin13Atom0767 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0771 chi ∧
      PredecessorHalfFin13Atom0790 chi ∧
      PredecessorHalfFin13Atom0942 chi ∧
      PredecessorHalfFin13Atom0943 chi ∧
      PredecessorHalfFin13Atom0946 chi ∧
      PredecessorHalfFin13Atom0965 chi ∧
      PredecessorHalfFin13Atom0985 chi) ∨
      ((PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0987 chi) ∨
      (PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0947 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0989 chi))) ∨
      ((PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0948 chi ∧
      PredecessorHalfFin13Atom0950 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0991 chi) ∨
      ((PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0745 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0752 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0777 chi ∧
      PredecessorHalfFin13Atom0779 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0952 chi ∧
      PredecessorHalfFin13Atom0954 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0993 chi) ∨
      (PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0951 chi ∧
      PredecessorHalfFin13Atom0953 chi ∧
      PredecessorHalfFin13Atom0955 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0994 chi)))) ∨
      (((PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0749 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0752 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0958 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0997 chi) ∨
      ((PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0957 chi ∧
      PredecessorHalfFin13Atom0959 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0998 chi) ∨
      (PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0749 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0756 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0787 chi ∧
      PredecessorHalfFin13Atom0791 chi ∧
      PredecessorHalfFin13Atom0960 chi ∧
      PredecessorHalfFin13Atom0961 chi ∧
      PredecessorHalfFin13Atom0962 chi ∧
      PredecessorHalfFin13Atom0966 chi ∧
      PredecessorHalfFin13Atom1000 chi))) ∨
      ((PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0752 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0756 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0790 chi ∧
      PredecessorHalfFin13Atom0791 chi ∧
      PredecessorHalfFin13Atom0963 chi ∧
      PredecessorHalfFin13Atom0964 chi ∧
      PredecessorHalfFin13Atom0965 chi ∧
      PredecessorHalfFin13Atom0966 chi ∧
      PredecessorHalfFin13Atom1001 chi) ∨
      ((PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0987 chi) ∨
      (PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0967 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0989 chi))))) ∨
      ((((PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0968 chi ∧
      PredecessorHalfFin13Atom0970 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0991 chi) ∨
      ((PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0971 chi ∧
      PredecessorHalfFin13Atom0973 chi ∧
      PredecessorHalfFin13Atom0975 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0994 chi) ∨
      (PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0764 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0767 chi ∧
      PredecessorHalfFin13Atom0769 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0978 chi ∧
      PredecessorHalfFin13Atom0980 chi ∧
      PredecessorHalfFin13Atom0983 chi ∧
      PredecessorHalfFin13Atom0997 chi))) ∨
      ((PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0977 chi ∧
      PredecessorHalfFin13Atom0979 chi ∧
      PredecessorHalfFin13Atom0981 chi ∧
      PredecessorHalfFin13Atom0984 chi ∧
      PredecessorHalfFin13Atom0998 chi) ∨
      ((PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0777 chi ∧
      PredecessorHalfFin13Atom0779 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0987 chi ∧
      PredecessorHalfFin13Atom0988 chi ∧
      PredecessorHalfFin13Atom0990 chi ∧
      PredecessorHalfFin13Atom0993 chi ∧
      PredecessorHalfFin13Atom0997 chi) ∨
      (PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0987 chi ∧
      PredecessorHalfFin13Atom0989 chi ∧
      PredecessorHalfFin13Atom0991 chi ∧
      PredecessorHalfFin13Atom0994 chi ∧
      PredecessorHalfFin13Atom0998 chi)))) ∨
      (((PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0779 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0781 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0787 chi ∧
      PredecessorHalfFin13Atom0791 chi ∧
      PredecessorHalfFin13Atom0990 chi ∧
      PredecessorHalfFin13Atom0991 chi ∧
      PredecessorHalfFin13Atom0992 chi ∧
      PredecessorHalfFin13Atom0996 chi ∧
      PredecessorHalfFin13Atom1000 chi) ∨
      ((PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0932 chi) ∨
      (PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0933 chi))) ∨
      ((PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0934 chi) ∨
      ((PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0799 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0936 chi) ∨
      (PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0937 chi)))))) ∨
      (((((PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0938 chi) ∨
      ((PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0800 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0940 chi) ∨
      (PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0941 chi))) ∨
      ((PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0824 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0880 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0942 chi) ∨
      ((PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0943 chi) ∨
      (PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0803 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0824 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0853 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0880 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0944 chi)))) ∨
      (((PredecessorHalfFin13Atom0792 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0945 chi) ∨
      ((PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0947 chi) ∨
      (PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0948 chi))) ∨
      ((PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0949 chi) ∨
      ((PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0950 chi) ∨
      (PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0951 chi))))) ∨
      ((((PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0952 chi) ∨
      ((PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0953 chi) ∨
      (PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0863 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0919 chi ∧
      PredecessorHalfFin13Atom0954 chi))) ∨
      ((PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0955 chi) ∨
      ((PredecessorHalfFin13Atom0793 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0819 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0840 chi ∧
      PredecessorHalfFin13Atom0865 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0896 chi ∧
      PredecessorHalfFin13Atom0921 chi ∧
      PredecessorHalfFin13Atom0956 chi) ∨
      (PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0957 chi)))) ∨
      (((PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0867 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0958 chi) ∨
      ((PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0959 chi) ∨
      (PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0869 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0960 chi))) ∨
      (((PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0961 chi) ∨
      (PredecessorHalfFin13Atom0794 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0819 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0840 chi ∧
      PredecessorHalfFin13Atom0871 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0896 chi ∧
      PredecessorHalfFin13Atom0927 chi ∧
      PredecessorHalfFin13Atom0962 chi)) ∨
      ((PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0797 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0928 chi ∧
      PredecessorHalfFin13Atom0963 chi) ∨
      (PredecessorHalfFin13Atom0795 chi ∧
      PredecessorHalfFin13Atom0796 chi ∧
      PredecessorHalfFin13Atom0798 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0964 chi))))))))) := by
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
              exact predecessorHalfFin13_clause26278 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26279 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26280 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26281 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26282 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26284 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26286 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26288 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26290 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26291 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26292 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26295 chi hnoStrong hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26298 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26299 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26301 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26302 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26303 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26304 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26306 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26308 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26309 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26310 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26311 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26312 chi hnoStrong hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26314 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26315 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26316 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26318 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26319 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26320 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26321 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26322 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26325 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26326 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26328 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26329 chi hnoStrong hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26330 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26332 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26333 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26334 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26336 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26337 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26339 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26340 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26341 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26343 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26345 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26347 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26350 chi hnoStrong hbad
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
              exact predecessorHalfFin13_clause26351 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26353 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26355 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26357 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26359 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26360 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26363 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26364 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26366 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26367 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26368 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26370 chi hnoStrong hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26372 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26375 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26378 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26379 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26383 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26384 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26386 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26389 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26390 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26391 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26393 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26394 chi hnoStrong hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26395 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26397 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26398 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26399 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26400 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26401 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26402 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26404 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26405 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26406 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26407 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26408 chi hnoStrong hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26409 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26410 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26411 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26412 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26413 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26414 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause26415 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26416 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26417 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26418 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26419 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause26420 chi hnoStrong hbad
              ·
                exact predecessorHalfFin13_clause26421 chi hnoStrong hbad

end ErdosSzekeres

end
