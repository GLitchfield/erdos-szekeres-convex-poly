module

public import ErdosSzekeres.Fin15AnchoredClauseChunk228
public import ErdosSzekeres.Fin15AnchoredClauseChunk229
public import ErdosSzekeres.Fin15AnchoredClauseChunk230

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 116. -/

theorem fin15Anchored_rejectSemanticSegment116
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom4715 chi) ∨
      ((Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom4716 chi) ∨
      (Fin15AnchoredAtom2703 chi ∧
      Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom2711 chi ∧
      Fin15AnchoredAtom2736 chi ∧
      Fin15AnchoredAtom2771 chi ∧
      Fin15AnchoredAtom4717 chi))) ∨
      (((Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom4720 chi) ∨
      (Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom4721 chi)) ∨
      ((Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom4722 chi) ∨
      (Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom4726 chi)))) ∨
      ((((Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom4727 chi) ∨
      (Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom4728 chi)) ∨
      ((Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom4732 chi) ∨
      (Fin15AnchoredAtom2717 chi ∧
      Fin15AnchoredAtom2719 chi ∧
      Fin15AnchoredAtom2723 chi ∧
      Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom4734 chi))) ∨
      (((Fin15AnchoredAtom2717 chi ∧
      Fin15AnchoredAtom2720 chi ∧
      Fin15AnchoredAtom2724 chi ∧
      Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom2789 chi ∧
      Fin15AnchoredAtom4735 chi) ∨
      (Fin15AnchoredAtom2719 chi ∧
      Fin15AnchoredAtom2720 chi ∧
      Fin15AnchoredAtom2729 chi ∧
      Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom2794 chi ∧
      Fin15AnchoredAtom4740 chi)) ∨
      ((Fin15AnchoredAtom2719 chi ∧
      Fin15AnchoredAtom2721 chi ∧
      Fin15AnchoredAtom2730 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom4741 chi) ∨
      (Fin15AnchoredAtom2720 chi ∧
      Fin15AnchoredAtom2721 chi ∧
      Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom4742 chi))))) ∨
      (((((Fin15AnchoredAtom2723 chi ∧
      Fin15AnchoredAtom2724 chi ∧
      Fin15AnchoredAtom2729 chi ∧
      Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom2800 chi ∧
      Fin15AnchoredAtom4746 chi) ∨
      (Fin15AnchoredAtom2723 chi ∧
      Fin15AnchoredAtom2725 chi ∧
      Fin15AnchoredAtom2730 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom4747 chi)) ∨
      ((Fin15AnchoredAtom2724 chi ∧
      Fin15AnchoredAtom2725 chi ∧
      Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom2802 chi ∧
      Fin15AnchoredAtom4748 chi) ∨
      (Fin15AnchoredAtom2729 chi ∧
      Fin15AnchoredAtom2730 chi ∧
      Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom4752 chi))) ∨
      (((Fin15AnchoredAtom2732 chi ∧
      Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom2736 chi ∧
      Fin15AnchoredAtom2742 chi ∧
      Fin15AnchoredAtom2807 chi ∧
      Fin15AnchoredAtom4753 chi) ∨
      (Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom4756 chi)) ∨
      ((Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom4757 chi) ∨
      (Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom4758 chi)))) ∨
      ((((Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom4762 chi) ∨
      (Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom4766 chi)) ∨
      ((Fin15AnchoredAtom2752 chi ∧
      Fin15AnchoredAtom2754 chi ∧
      Fin15AnchoredAtom2758 chi ∧
      Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom4769 chi) ∨
      (Fin15AnchoredAtom2752 chi ∧
      Fin15AnchoredAtom2755 chi ∧
      Fin15AnchoredAtom2759 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom2789 chi ∧
      Fin15AnchoredAtom4770 chi))) ∨
      (((Fin15AnchoredAtom2752 chi ∧
      Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom2760 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom2790 chi ∧
      Fin15AnchoredAtom4771 chi) ∨
      (Fin15AnchoredAtom2754 chi ∧
      Fin15AnchoredAtom2755 chi ∧
      Fin15AnchoredAtom2764 chi ∧
      Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom2794 chi ∧
      Fin15AnchoredAtom4775 chi)) ∨
      ((Fin15AnchoredAtom2754 chi ∧
      Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom2765 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom4776 chi) ∨
      (Fin15AnchoredAtom2755 chi ∧
      Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom2766 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom4777 chi)))))) ∨
      ((((((Fin15AnchoredAtom2758 chi ∧
      Fin15AnchoredAtom2759 chi ∧
      Fin15AnchoredAtom2764 chi ∧
      Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom2800 chi ∧
      Fin15AnchoredAtom4781 chi) ∨
      (Fin15AnchoredAtom2758 chi ∧
      Fin15AnchoredAtom2760 chi ∧
      Fin15AnchoredAtom2765 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom4782 chi)) ∨
      ((Fin15AnchoredAtom2759 chi ∧
      Fin15AnchoredAtom2760 chi ∧
      Fin15AnchoredAtom2766 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom2802 chi ∧
      Fin15AnchoredAtom4783 chi) ∨
      (Fin15AnchoredAtom2764 chi ∧
      Fin15AnchoredAtom2765 chi ∧
      Fin15AnchoredAtom2766 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom4787 chi))) ∨
      (((Fin15AnchoredAtom2767 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom2772 chi ∧
      Fin15AnchoredAtom2778 chi ∧
      Fin15AnchoredAtom2808 chi ∧
      Fin15AnchoredAtom4789 chi) ∨
      (Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom4791 chi)) ∨
      ((Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom4792 chi) ∨
      (Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom4793 chi)))) ∨
      ((((Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom4797 chi) ∨
      (Fin15AnchoredAtom2777 chi ∧
      Fin15AnchoredAtom2779 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom2784 chi ∧
      Fin15AnchoredAtom2818 chi ∧
      Fin15AnchoredAtom4799 chi)) ∨
      ((Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom4801 chi) ∨
      (Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom2789 chi ∧
      Fin15AnchoredAtom2794 chi ∧
      Fin15AnchoredAtom2800 chi ∧
      Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom4806 chi))) ∨
      (((Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom2790 chi ∧
      Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom4807 chi) ∨
      (Fin15AnchoredAtom2789 chi ∧
      Fin15AnchoredAtom2790 chi ∧
      Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom2802 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom4808 chi)) ∨
      ((Fin15AnchoredAtom2794 chi ∧
      Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom4812 chi) ∨
      (Fin15AnchoredAtom2800 chi ∧
      Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom2802 chi ∧
      Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom4816 chi))))) ∨
      (((((Fin15AnchoredAtom2807 chi ∧
      Fin15AnchoredAtom2809 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom2814 chi ∧
      Fin15AnchoredAtom2818 chi ∧
      Fin15AnchoredAtom4819 chi) ∨
      (Fin15AnchoredAtom2808 chi ∧
      Fin15AnchoredAtom2809 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom2815 chi ∧
      Fin15AnchoredAtom2819 chi ∧
      Fin15AnchoredAtom4820 chi)) ∨
      ((Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom4821 chi) ∨
      (Fin15AnchoredAtom2822 chi ∧
      Fin15AnchoredAtom2823 chi ∧
      Fin15AnchoredAtom2832 chi ∧
      Fin15AnchoredAtom2877 chi ∧
      Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom3537 chi))) ∨
      (((Fin15AnchoredAtom2822 chi ∧
      Fin15AnchoredAtom2824 chi ∧
      Fin15AnchoredAtom2833 chi ∧
      Fin15AnchoredAtom2878 chi ∧
      Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom3538 chi) ∨
      (Fin15AnchoredAtom2822 chi ∧
      Fin15AnchoredAtom2826 chi ∧
      Fin15AnchoredAtom2835 chi ∧
      Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom3045 chi ∧
      Fin15AnchoredAtom3540 chi)) ∨
      ((Fin15AnchoredAtom2822 chi ∧
      Fin15AnchoredAtom2827 chi ∧
      Fin15AnchoredAtom2836 chi ∧
      Fin15AnchoredAtom2881 chi ∧
      Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom3541 chi) ∨
      (Fin15AnchoredAtom2822 chi ∧
      Fin15AnchoredAtom2829 chi ∧
      Fin15AnchoredAtom2838 chi ∧
      Fin15AnchoredAtom2883 chi ∧
      Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom3543 chi)))) ∨
      ((((Fin15AnchoredAtom2822 chi ∧
      Fin15AnchoredAtom2830 chi ∧
      Fin15AnchoredAtom2839 chi ∧
      Fin15AnchoredAtom2884 chi ∧
      Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom3544 chi) ∨
      (Fin15AnchoredAtom2822 chi ∧
      Fin15AnchoredAtom2831 chi ∧
      Fin15AnchoredAtom2840 chi ∧
      Fin15AnchoredAtom2885 chi ∧
      Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom3545 chi)) ∨
      ((Fin15AnchoredAtom2823 chi ∧
      Fin15AnchoredAtom2824 chi ∧
      Fin15AnchoredAtom2841 chi ∧
      Fin15AnchoredAtom2886 chi ∧
      Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom3546 chi) ∨
      (Fin15AnchoredAtom2823 chi ∧
      Fin15AnchoredAtom2826 chi ∧
      Fin15AnchoredAtom2843 chi ∧
      Fin15AnchoredAtom2888 chi ∧
      Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom3548 chi))) ∨
      (((Fin15AnchoredAtom2823 chi ∧
      Fin15AnchoredAtom2827 chi ∧
      Fin15AnchoredAtom2844 chi ∧
      Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom3549 chi) ∨
      (Fin15AnchoredAtom2823 chi ∧
      Fin15AnchoredAtom2829 chi ∧
      Fin15AnchoredAtom2846 chi ∧
      Fin15AnchoredAtom2891 chi ∧
      Fin15AnchoredAtom3056 chi ∧
      Fin15AnchoredAtom3551 chi)) ∨
      ((Fin15AnchoredAtom2823 chi ∧
      Fin15AnchoredAtom2830 chi ∧
      Fin15AnchoredAtom2847 chi ∧
      Fin15AnchoredAtom2892 chi ∧
      Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom3552 chi) ∨
      (Fin15AnchoredAtom2823 chi ∧
      Fin15AnchoredAtom2831 chi ∧
      Fin15AnchoredAtom2848 chi ∧
      Fin15AnchoredAtom2893 chi ∧
      Fin15AnchoredAtom3058 chi ∧
      Fin15AnchoredAtom3553 chi))))))) ∨
      ((((((Fin15AnchoredAtom2824 chi ∧
      Fin15AnchoredAtom2826 chi ∧
      Fin15AnchoredAtom2850 chi ∧
      Fin15AnchoredAtom2895 chi ∧
      Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom3555 chi) ∨
      ((Fin15AnchoredAtom2824 chi ∧
      Fin15AnchoredAtom2827 chi ∧
      Fin15AnchoredAtom2851 chi ∧
      Fin15AnchoredAtom2896 chi ∧
      Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom3556 chi) ∨
      (Fin15AnchoredAtom2824 chi ∧
      Fin15AnchoredAtom2829 chi ∧
      Fin15AnchoredAtom2853 chi ∧
      Fin15AnchoredAtom2898 chi ∧
      Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3558 chi))) ∨
      (((Fin15AnchoredAtom2824 chi ∧
      Fin15AnchoredAtom2830 chi ∧
      Fin15AnchoredAtom2854 chi ∧
      Fin15AnchoredAtom2899 chi ∧
      Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom3559 chi) ∨
      (Fin15AnchoredAtom2824 chi ∧
      Fin15AnchoredAtom2831 chi ∧
      Fin15AnchoredAtom2855 chi ∧
      Fin15AnchoredAtom2900 chi ∧
      Fin15AnchoredAtom3065 chi ∧
      Fin15AnchoredAtom3560 chi)) ∨
      ((Fin15AnchoredAtom2826 chi ∧
      Fin15AnchoredAtom2827 chi ∧
      Fin15AnchoredAtom2862 chi ∧
      Fin15AnchoredAtom2907 chi ∧
      Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom3567 chi) ∨
      (Fin15AnchoredAtom2826 chi ∧
      Fin15AnchoredAtom2829 chi ∧
      Fin15AnchoredAtom2864 chi ∧
      Fin15AnchoredAtom2909 chi ∧
      Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom3569 chi)))) ∨
      ((((Fin15AnchoredAtom2826 chi ∧
      Fin15AnchoredAtom2830 chi ∧
      Fin15AnchoredAtom2865 chi ∧
      Fin15AnchoredAtom2910 chi ∧
      Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom3570 chi) ∨
      (Fin15AnchoredAtom2826 chi ∧
      Fin15AnchoredAtom2831 chi ∧
      Fin15AnchoredAtom2866 chi ∧
      Fin15AnchoredAtom2911 chi ∧
      Fin15AnchoredAtom3076 chi ∧
      Fin15AnchoredAtom3571 chi)) ∨
      ((Fin15AnchoredAtom2827 chi ∧
      Fin15AnchoredAtom2829 chi ∧
      Fin15AnchoredAtom2868 chi ∧
      Fin15AnchoredAtom2913 chi ∧
      Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom3573 chi) ∨
      (Fin15AnchoredAtom2827 chi ∧
      Fin15AnchoredAtom2830 chi ∧
      Fin15AnchoredAtom2869 chi ∧
      Fin15AnchoredAtom2914 chi ∧
      Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom3574 chi))) ∨
      (((Fin15AnchoredAtom2827 chi ∧
      Fin15AnchoredAtom2831 chi ∧
      Fin15AnchoredAtom2870 chi ∧
      Fin15AnchoredAtom2915 chi ∧
      Fin15AnchoredAtom3080 chi ∧
      Fin15AnchoredAtom3575 chi) ∨
      (Fin15AnchoredAtom2829 chi ∧
      Fin15AnchoredAtom2830 chi ∧
      Fin15AnchoredAtom2874 chi ∧
      Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom3579 chi)) ∨
      ((Fin15AnchoredAtom2829 chi ∧
      Fin15AnchoredAtom2831 chi ∧
      Fin15AnchoredAtom2875 chi ∧
      Fin15AnchoredAtom2920 chi ∧
      Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom3580 chi) ∨
      (Fin15AnchoredAtom2830 chi ∧
      Fin15AnchoredAtom2831 chi ∧
      Fin15AnchoredAtom2876 chi ∧
      Fin15AnchoredAtom2921 chi ∧
      Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom3581 chi))))) ∨
      (((((Fin15AnchoredAtom2832 chi ∧
      Fin15AnchoredAtom2833 chi ∧
      Fin15AnchoredAtom2841 chi ∧
      Fin15AnchoredAtom2922 chi ∧
      Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom3582 chi) ∨
      (Fin15AnchoredAtom2832 chi ∧
      Fin15AnchoredAtom2835 chi ∧
      Fin15AnchoredAtom2843 chi ∧
      Fin15AnchoredAtom2924 chi ∧
      Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom3584 chi)) ∨
      ((Fin15AnchoredAtom2832 chi ∧
      Fin15AnchoredAtom2836 chi ∧
      Fin15AnchoredAtom2844 chi ∧
      Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom3090 chi ∧
      Fin15AnchoredAtom3585 chi) ∨
      (Fin15AnchoredAtom2832 chi ∧
      Fin15AnchoredAtom2838 chi ∧
      Fin15AnchoredAtom2846 chi ∧
      Fin15AnchoredAtom2927 chi ∧
      Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom3587 chi))) ∨
      (((Fin15AnchoredAtom2832 chi ∧
      Fin15AnchoredAtom2839 chi ∧
      Fin15AnchoredAtom2847 chi ∧
      Fin15AnchoredAtom2928 chi ∧
      Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom3588 chi) ∨
      (Fin15AnchoredAtom2832 chi ∧
      Fin15AnchoredAtom2840 chi ∧
      Fin15AnchoredAtom2848 chi ∧
      Fin15AnchoredAtom2929 chi ∧
      Fin15AnchoredAtom3094 chi ∧
      Fin15AnchoredAtom3589 chi)) ∨
      ((Fin15AnchoredAtom2833 chi ∧
      Fin15AnchoredAtom2835 chi ∧
      Fin15AnchoredAtom2850 chi ∧
      Fin15AnchoredAtom2931 chi ∧
      Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom3591 chi) ∨
      (Fin15AnchoredAtom2833 chi ∧
      Fin15AnchoredAtom2836 chi ∧
      Fin15AnchoredAtom2851 chi ∧
      Fin15AnchoredAtom2932 chi ∧
      Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom3592 chi)))) ∨
      ((((Fin15AnchoredAtom2833 chi ∧
      Fin15AnchoredAtom2838 chi ∧
      Fin15AnchoredAtom2853 chi ∧
      Fin15AnchoredAtom2934 chi ∧
      Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom3594 chi) ∨
      (Fin15AnchoredAtom2833 chi ∧
      Fin15AnchoredAtom2839 chi ∧
      Fin15AnchoredAtom2854 chi ∧
      Fin15AnchoredAtom2935 chi ∧
      Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom3595 chi)) ∨
      ((Fin15AnchoredAtom2833 chi ∧
      Fin15AnchoredAtom2840 chi ∧
      Fin15AnchoredAtom2855 chi ∧
      Fin15AnchoredAtom2936 chi ∧
      Fin15AnchoredAtom3101 chi ∧
      Fin15AnchoredAtom3596 chi) ∨
      (Fin15AnchoredAtom2835 chi ∧
      Fin15AnchoredAtom2836 chi ∧
      Fin15AnchoredAtom2862 chi ∧
      Fin15AnchoredAtom2943 chi ∧
      Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom3603 chi))) ∨
      (((Fin15AnchoredAtom2835 chi ∧
      Fin15AnchoredAtom2838 chi ∧
      Fin15AnchoredAtom2864 chi ∧
      Fin15AnchoredAtom2945 chi ∧
      Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom3605 chi) ∨
      (Fin15AnchoredAtom2835 chi ∧
      Fin15AnchoredAtom2839 chi ∧
      Fin15AnchoredAtom2865 chi ∧
      Fin15AnchoredAtom2946 chi ∧
      Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom3606 chi)) ∨
      ((Fin15AnchoredAtom2835 chi ∧
      Fin15AnchoredAtom2840 chi ∧
      Fin15AnchoredAtom2866 chi ∧
      Fin15AnchoredAtom2947 chi ∧
      Fin15AnchoredAtom3112 chi ∧
      Fin15AnchoredAtom3607 chi) ∨
      (Fin15AnchoredAtom2836 chi ∧
      Fin15AnchoredAtom2838 chi ∧
      Fin15AnchoredAtom2868 chi ∧
      Fin15AnchoredAtom2949 chi ∧
      Fin15AnchoredAtom3114 chi ∧
      Fin15AnchoredAtom3609 chi)))))) ∨
      ((((((Fin15AnchoredAtom2836 chi ∧
      Fin15AnchoredAtom2839 chi ∧
      Fin15AnchoredAtom2869 chi ∧
      Fin15AnchoredAtom2950 chi ∧
      Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom3610 chi) ∨
      (Fin15AnchoredAtom2836 chi ∧
      Fin15AnchoredAtom2840 chi ∧
      Fin15AnchoredAtom2870 chi ∧
      Fin15AnchoredAtom2951 chi ∧
      Fin15AnchoredAtom3116 chi ∧
      Fin15AnchoredAtom3611 chi)) ∨
      ((Fin15AnchoredAtom2838 chi ∧
      Fin15AnchoredAtom2839 chi ∧
      Fin15AnchoredAtom2874 chi ∧
      Fin15AnchoredAtom2955 chi ∧
      Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom3615 chi) ∨
      (Fin15AnchoredAtom2838 chi ∧
      Fin15AnchoredAtom2840 chi ∧
      Fin15AnchoredAtom2875 chi ∧
      Fin15AnchoredAtom2956 chi ∧
      Fin15AnchoredAtom3121 chi ∧
      Fin15AnchoredAtom3616 chi))) ∨
      (((Fin15AnchoredAtom2839 chi ∧
      Fin15AnchoredAtom2840 chi ∧
      Fin15AnchoredAtom2876 chi ∧
      Fin15AnchoredAtom2957 chi ∧
      Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom3617 chi) ∨
      (Fin15AnchoredAtom2841 chi ∧
      Fin15AnchoredAtom2843 chi ∧
      Fin15AnchoredAtom2850 chi ∧
      Fin15AnchoredAtom2959 chi ∧
      Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom3619 chi)) ∨
      ((Fin15AnchoredAtom2841 chi ∧
      Fin15AnchoredAtom2844 chi ∧
      Fin15AnchoredAtom2851 chi ∧
      Fin15AnchoredAtom2960 chi ∧
      Fin15AnchoredAtom3125 chi ∧
      Fin15AnchoredAtom3620 chi) ∨
      (Fin15AnchoredAtom2841 chi ∧
      Fin15AnchoredAtom2846 chi ∧
      Fin15AnchoredAtom2853 chi ∧
      Fin15AnchoredAtom2962 chi ∧
      Fin15AnchoredAtom3127 chi ∧
      Fin15AnchoredAtom3622 chi)))) ∨
      ((((Fin15AnchoredAtom2841 chi ∧
      Fin15AnchoredAtom2847 chi ∧
      Fin15AnchoredAtom2854 chi ∧
      Fin15AnchoredAtom2963 chi ∧
      Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom3623 chi) ∨
      (Fin15AnchoredAtom2841 chi ∧
      Fin15AnchoredAtom2848 chi ∧
      Fin15AnchoredAtom2855 chi ∧
      Fin15AnchoredAtom2964 chi ∧
      Fin15AnchoredAtom3129 chi ∧
      Fin15AnchoredAtom3624 chi)) ∨
      ((Fin15AnchoredAtom2843 chi ∧
      Fin15AnchoredAtom2844 chi ∧
      Fin15AnchoredAtom2862 chi ∧
      Fin15AnchoredAtom2971 chi ∧
      Fin15AnchoredAtom3136 chi ∧
      Fin15AnchoredAtom3631 chi) ∨
      (Fin15AnchoredAtom2843 chi ∧
      Fin15AnchoredAtom2846 chi ∧
      Fin15AnchoredAtom2864 chi ∧
      Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom3633 chi))) ∨
      (((Fin15AnchoredAtom2843 chi ∧
      Fin15AnchoredAtom2847 chi ∧
      Fin15AnchoredAtom2865 chi ∧
      Fin15AnchoredAtom2974 chi ∧
      Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom3634 chi) ∨
      (Fin15AnchoredAtom2843 chi ∧
      Fin15AnchoredAtom2848 chi ∧
      Fin15AnchoredAtom2866 chi ∧
      Fin15AnchoredAtom2975 chi ∧
      Fin15AnchoredAtom3140 chi ∧
      Fin15AnchoredAtom3635 chi)) ∨
      ((Fin15AnchoredAtom2844 chi ∧
      Fin15AnchoredAtom2846 chi ∧
      Fin15AnchoredAtom2868 chi ∧
      Fin15AnchoredAtom2977 chi ∧
      Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom3637 chi) ∨
      (Fin15AnchoredAtom2844 chi ∧
      Fin15AnchoredAtom2847 chi ∧
      Fin15AnchoredAtom2869 chi ∧
      Fin15AnchoredAtom2978 chi ∧
      Fin15AnchoredAtom3143 chi ∧
      Fin15AnchoredAtom3638 chi))))) ∨
      (((((Fin15AnchoredAtom2844 chi ∧
      Fin15AnchoredAtom2848 chi ∧
      Fin15AnchoredAtom2870 chi ∧
      Fin15AnchoredAtom2979 chi ∧
      Fin15AnchoredAtom3144 chi ∧
      Fin15AnchoredAtom3639 chi) ∨
      (Fin15AnchoredAtom2846 chi ∧
      Fin15AnchoredAtom2847 chi ∧
      Fin15AnchoredAtom2874 chi ∧
      Fin15AnchoredAtom2983 chi ∧
      Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom3643 chi)) ∨
      ((Fin15AnchoredAtom2846 chi ∧
      Fin15AnchoredAtom2848 chi ∧
      Fin15AnchoredAtom2875 chi ∧
      Fin15AnchoredAtom2984 chi ∧
      Fin15AnchoredAtom3149 chi ∧
      Fin15AnchoredAtom3644 chi) ∨
      (Fin15AnchoredAtom2847 chi ∧
      Fin15AnchoredAtom2848 chi ∧
      Fin15AnchoredAtom2876 chi ∧
      Fin15AnchoredAtom2985 chi ∧
      Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom3645 chi))) ∨
      (((Fin15AnchoredAtom2850 chi ∧
      Fin15AnchoredAtom2851 chi ∧
      Fin15AnchoredAtom2862 chi ∧
      Fin15AnchoredAtom2992 chi ∧
      Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom3652 chi) ∨
      (Fin15AnchoredAtom2850 chi ∧
      Fin15AnchoredAtom2853 chi ∧
      Fin15AnchoredAtom2864 chi ∧
      Fin15AnchoredAtom2994 chi ∧
      Fin15AnchoredAtom3159 chi ∧
      Fin15AnchoredAtom3654 chi)) ∨
      ((Fin15AnchoredAtom2850 chi ∧
      Fin15AnchoredAtom2854 chi ∧
      Fin15AnchoredAtom2865 chi ∧
      Fin15AnchoredAtom2995 chi ∧
      Fin15AnchoredAtom3160 chi ∧
      Fin15AnchoredAtom3655 chi) ∨
      (Fin15AnchoredAtom2850 chi ∧
      Fin15AnchoredAtom2855 chi ∧
      Fin15AnchoredAtom2866 chi ∧
      Fin15AnchoredAtom2996 chi ∧
      Fin15AnchoredAtom3161 chi ∧
      Fin15AnchoredAtom3656 chi)))) ∨
      ((((Fin15AnchoredAtom2851 chi ∧
      Fin15AnchoredAtom2853 chi ∧
      Fin15AnchoredAtom2868 chi ∧
      Fin15AnchoredAtom2998 chi ∧
      Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom3658 chi) ∨
      (Fin15AnchoredAtom2851 chi ∧
      Fin15AnchoredAtom2854 chi ∧
      Fin15AnchoredAtom2869 chi ∧
      Fin15AnchoredAtom2999 chi ∧
      Fin15AnchoredAtom3164 chi ∧
      Fin15AnchoredAtom3659 chi)) ∨
      ((Fin15AnchoredAtom2851 chi ∧
      Fin15AnchoredAtom2855 chi ∧
      Fin15AnchoredAtom2870 chi ∧
      Fin15AnchoredAtom3000 chi ∧
      Fin15AnchoredAtom3165 chi ∧
      Fin15AnchoredAtom3660 chi) ∨
      (Fin15AnchoredAtom2853 chi ∧
      Fin15AnchoredAtom2854 chi ∧
      Fin15AnchoredAtom2874 chi ∧
      Fin15AnchoredAtom3004 chi ∧
      Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom3664 chi))) ∨
      (((Fin15AnchoredAtom2853 chi ∧
      Fin15AnchoredAtom2855 chi ∧
      Fin15AnchoredAtom2875 chi ∧
      Fin15AnchoredAtom3005 chi ∧
      Fin15AnchoredAtom3170 chi ∧
      Fin15AnchoredAtom3665 chi) ∨
      (Fin15AnchoredAtom2854 chi ∧
      Fin15AnchoredAtom2855 chi ∧
      Fin15AnchoredAtom2876 chi ∧
      Fin15AnchoredAtom3006 chi ∧
      Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom3666 chi)) ∨
      ((Fin15AnchoredAtom2862 chi ∧
      Fin15AnchoredAtom2864 chi ∧
      Fin15AnchoredAtom2868 chi ∧
      Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom3188 chi ∧
      Fin15AnchoredAtom3683 chi) ∨
      (Fin15AnchoredAtom2862 chi ∧
      Fin15AnchoredAtom2865 chi ∧
      Fin15AnchoredAtom2869 chi ∧
      Fin15AnchoredAtom3024 chi ∧
      Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom3684 chi)))))))) ∨
      (((((((Fin15AnchoredAtom2862 chi ∧
      Fin15AnchoredAtom2866 chi ∧
      Fin15AnchoredAtom2870 chi ∧
      Fin15AnchoredAtom3025 chi ∧
      Fin15AnchoredAtom3190 chi ∧
      Fin15AnchoredAtom3685 chi) ∨
      ((Fin15AnchoredAtom2864 chi ∧
      Fin15AnchoredAtom2865 chi ∧
      Fin15AnchoredAtom2874 chi ∧
      Fin15AnchoredAtom3029 chi ∧
      Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom3689 chi) ∨
      (Fin15AnchoredAtom2864 chi ∧
      Fin15AnchoredAtom2866 chi ∧
      Fin15AnchoredAtom2875 chi ∧
      Fin15AnchoredAtom3030 chi ∧
      Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom3690 chi))) ∨
      (((Fin15AnchoredAtom2865 chi ∧
      Fin15AnchoredAtom2866 chi ∧
      Fin15AnchoredAtom2876 chi ∧
      Fin15AnchoredAtom3031 chi ∧
      Fin15AnchoredAtom3196 chi ∧
      Fin15AnchoredAtom3691 chi) ∨
      (Fin15AnchoredAtom2868 chi ∧
      Fin15AnchoredAtom2869 chi ∧
      Fin15AnchoredAtom2874 chi ∧
      Fin15AnchoredAtom3035 chi ∧
      Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom3695 chi)) ∨
      ((Fin15AnchoredAtom2868 chi ∧
      Fin15AnchoredAtom2870 chi ∧
      Fin15AnchoredAtom2875 chi ∧
      Fin15AnchoredAtom3036 chi ∧
      Fin15AnchoredAtom3201 chi ∧
      Fin15AnchoredAtom3696 chi) ∨
      (Fin15AnchoredAtom2869 chi ∧
      Fin15AnchoredAtom2870 chi ∧
      Fin15AnchoredAtom2876 chi ∧
      Fin15AnchoredAtom3037 chi ∧
      Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom3697 chi)))) ∨
      ((((Fin15AnchoredAtom2874 chi ∧
      Fin15AnchoredAtom2875 chi ∧
      Fin15AnchoredAtom2876 chi ∧
      Fin15AnchoredAtom3041 chi ∧
      Fin15AnchoredAtom3206 chi ∧
      Fin15AnchoredAtom3701 chi) ∨
      (Fin15AnchoredAtom2877 chi ∧
      Fin15AnchoredAtom2878 chi ∧
      Fin15AnchoredAtom2886 chi ∧
      Fin15AnchoredAtom2922 chi ∧
      Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom3702 chi)) ∨
      ((Fin15AnchoredAtom2877 chi ∧
      Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom2888 chi ∧
      Fin15AnchoredAtom2924 chi ∧
      Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom3704 chi) ∨
      (Fin15AnchoredAtom2877 chi ∧
      Fin15AnchoredAtom2881 chi ∧
      Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom3705 chi))) ∨
      (((Fin15AnchoredAtom2877 chi ∧
      Fin15AnchoredAtom2883 chi ∧
      Fin15AnchoredAtom2891 chi ∧
      Fin15AnchoredAtom2927 chi ∧
      Fin15AnchoredAtom3212 chi ∧
      Fin15AnchoredAtom3707 chi) ∨
      (Fin15AnchoredAtom2877 chi ∧
      Fin15AnchoredAtom2884 chi ∧
      Fin15AnchoredAtom2892 chi ∧
      Fin15AnchoredAtom2928 chi ∧
      Fin15AnchoredAtom3213 chi ∧
      Fin15AnchoredAtom3708 chi)) ∨
      ((Fin15AnchoredAtom2877 chi ∧
      Fin15AnchoredAtom2885 chi ∧
      Fin15AnchoredAtom2893 chi ∧
      Fin15AnchoredAtom2929 chi ∧
      Fin15AnchoredAtom3214 chi ∧
      Fin15AnchoredAtom3709 chi) ∨
      (Fin15AnchoredAtom2878 chi ∧
      Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom2895 chi ∧
      Fin15AnchoredAtom2931 chi ∧
      Fin15AnchoredAtom3216 chi ∧
      Fin15AnchoredAtom3711 chi))))) ∨
      (((((Fin15AnchoredAtom2878 chi ∧
      Fin15AnchoredAtom2881 chi ∧
      Fin15AnchoredAtom2896 chi ∧
      Fin15AnchoredAtom2932 chi ∧
      Fin15AnchoredAtom3217 chi ∧
      Fin15AnchoredAtom3712 chi) ∨
      (Fin15AnchoredAtom2878 chi ∧
      Fin15AnchoredAtom2883 chi ∧
      Fin15AnchoredAtom2898 chi ∧
      Fin15AnchoredAtom2934 chi ∧
      Fin15AnchoredAtom3219 chi ∧
      Fin15AnchoredAtom3714 chi)) ∨
      ((Fin15AnchoredAtom2878 chi ∧
      Fin15AnchoredAtom2884 chi ∧
      Fin15AnchoredAtom2899 chi ∧
      Fin15AnchoredAtom2935 chi ∧
      Fin15AnchoredAtom3220 chi ∧
      Fin15AnchoredAtom3715 chi) ∨
      (Fin15AnchoredAtom2878 chi ∧
      Fin15AnchoredAtom2885 chi ∧
      Fin15AnchoredAtom2900 chi ∧
      Fin15AnchoredAtom2936 chi ∧
      Fin15AnchoredAtom3221 chi ∧
      Fin15AnchoredAtom3716 chi))) ∨
      (((Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom2881 chi ∧
      Fin15AnchoredAtom2907 chi ∧
      Fin15AnchoredAtom2943 chi ∧
      Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom3723 chi) ∨
      (Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom2882 chi ∧
      Fin15AnchoredAtom2908 chi ∧
      Fin15AnchoredAtom2944 chi ∧
      Fin15AnchoredAtom3229 chi ∧
      Fin15AnchoredAtom3724 chi)) ∨
      ((Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom2883 chi ∧
      Fin15AnchoredAtom2909 chi ∧
      Fin15AnchoredAtom2945 chi ∧
      Fin15AnchoredAtom3230 chi ∧
      Fin15AnchoredAtom3725 chi) ∨
      (Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom2884 chi ∧
      Fin15AnchoredAtom2910 chi ∧
      Fin15AnchoredAtom2946 chi ∧
      Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom3726 chi)))) ∨
      ((((Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom2885 chi ∧
      Fin15AnchoredAtom2911 chi ∧
      Fin15AnchoredAtom2947 chi ∧
      Fin15AnchoredAtom3232 chi ∧
      Fin15AnchoredAtom3727 chi) ∨
      (Fin15AnchoredAtom2881 chi ∧
      Fin15AnchoredAtom2883 chi ∧
      Fin15AnchoredAtom2913 chi ∧
      Fin15AnchoredAtom2949 chi ∧
      Fin15AnchoredAtom3234 chi ∧
      Fin15AnchoredAtom3729 chi)) ∨
      ((Fin15AnchoredAtom2881 chi ∧
      Fin15AnchoredAtom2884 chi ∧
      Fin15AnchoredAtom2914 chi ∧
      Fin15AnchoredAtom2950 chi ∧
      Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom3730 chi) ∨
      (Fin15AnchoredAtom2881 chi ∧
      Fin15AnchoredAtom2885 chi ∧
      Fin15AnchoredAtom2915 chi ∧
      Fin15AnchoredAtom2951 chi ∧
      Fin15AnchoredAtom3236 chi ∧
      Fin15AnchoredAtom3731 chi))) ∨
      (((Fin15AnchoredAtom2883 chi ∧
      Fin15AnchoredAtom2884 chi ∧
      Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom2955 chi ∧
      Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom3735 chi) ∨
      (Fin15AnchoredAtom2883 chi ∧
      Fin15AnchoredAtom2885 chi ∧
      Fin15AnchoredAtom2920 chi ∧
      Fin15AnchoredAtom2956 chi ∧
      Fin15AnchoredAtom3241 chi ∧
      Fin15AnchoredAtom3736 chi)) ∨
      ((Fin15AnchoredAtom2884 chi ∧
      Fin15AnchoredAtom2885 chi ∧
      Fin15AnchoredAtom2921 chi ∧
      Fin15AnchoredAtom2957 chi ∧
      Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom3737 chi) ∨
      (Fin15AnchoredAtom2886 chi ∧
      Fin15AnchoredAtom2888 chi ∧
      Fin15AnchoredAtom2895 chi ∧
      Fin15AnchoredAtom2959 chi ∧
      Fin15AnchoredAtom3244 chi ∧
      Fin15AnchoredAtom3739 chi)))))) ∨
      ((((((Fin15AnchoredAtom2886 chi ∧
      Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom2896 chi ∧
      Fin15AnchoredAtom2960 chi ∧
      Fin15AnchoredAtom3245 chi ∧
      Fin15AnchoredAtom3740 chi) ∨
      (Fin15AnchoredAtom2886 chi ∧
      Fin15AnchoredAtom2891 chi ∧
      Fin15AnchoredAtom2898 chi ∧
      Fin15AnchoredAtom2962 chi ∧
      Fin15AnchoredAtom3247 chi ∧
      Fin15AnchoredAtom3742 chi)) ∨
      ((Fin15AnchoredAtom2886 chi ∧
      Fin15AnchoredAtom2892 chi ∧
      Fin15AnchoredAtom2899 chi ∧
      Fin15AnchoredAtom2963 chi ∧
      Fin15AnchoredAtom3248 chi ∧
      Fin15AnchoredAtom3743 chi) ∨
      (Fin15AnchoredAtom2886 chi ∧
      Fin15AnchoredAtom2893 chi ∧
      Fin15AnchoredAtom2900 chi ∧
      Fin15AnchoredAtom2964 chi ∧
      Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom3744 chi))) ∨
      (((Fin15AnchoredAtom2888 chi ∧
      Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom2907 chi ∧
      Fin15AnchoredAtom2971 chi ∧
      Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom3751 chi) ∨
      (Fin15AnchoredAtom2888 chi ∧
      Fin15AnchoredAtom2891 chi ∧
      Fin15AnchoredAtom2909 chi ∧
      Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom3258 chi ∧
      Fin15AnchoredAtom3753 chi)) ∨
      ((Fin15AnchoredAtom2888 chi ∧
      Fin15AnchoredAtom2892 chi ∧
      Fin15AnchoredAtom2910 chi ∧
      Fin15AnchoredAtom2974 chi ∧
      Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom3754 chi) ∨
      (Fin15AnchoredAtom2888 chi ∧
      Fin15AnchoredAtom2893 chi ∧
      Fin15AnchoredAtom2911 chi ∧
      Fin15AnchoredAtom2975 chi ∧
      Fin15AnchoredAtom3260 chi ∧
      Fin15AnchoredAtom3755 chi)))) ∨
      ((((Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom2890 chi ∧
      Fin15AnchoredAtom2912 chi ∧
      Fin15AnchoredAtom2976 chi ∧
      Fin15AnchoredAtom3261 chi ∧
      Fin15AnchoredAtom3756 chi) ∨
      (Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom2891 chi ∧
      Fin15AnchoredAtom2913 chi ∧
      Fin15AnchoredAtom2977 chi ∧
      Fin15AnchoredAtom3262 chi ∧
      Fin15AnchoredAtom3757 chi)) ∨
      ((Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom2892 chi ∧
      Fin15AnchoredAtom2914 chi ∧
      Fin15AnchoredAtom2978 chi ∧
      Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom3758 chi) ∨
      (Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom2893 chi ∧
      Fin15AnchoredAtom2915 chi ∧
      Fin15AnchoredAtom2979 chi ∧
      Fin15AnchoredAtom3264 chi ∧
      Fin15AnchoredAtom3759 chi))) ∨
      (((Fin15AnchoredAtom2891 chi ∧
      Fin15AnchoredAtom2892 chi ∧
      Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom2983 chi ∧
      Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom3763 chi) ∨
      (Fin15AnchoredAtom2891 chi ∧
      Fin15AnchoredAtom2893 chi ∧
      Fin15AnchoredAtom2920 chi ∧
      Fin15AnchoredAtom2984 chi ∧
      Fin15AnchoredAtom3269 chi ∧
      Fin15AnchoredAtom3764 chi)) ∨
      ((Fin15AnchoredAtom2892 chi ∧
      Fin15AnchoredAtom2893 chi ∧
      Fin15AnchoredAtom2921 chi ∧
      Fin15AnchoredAtom2985 chi ∧
      Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom3765 chi) ∨
      (Fin15AnchoredAtom2895 chi ∧
      Fin15AnchoredAtom2896 chi ∧
      Fin15AnchoredAtom2907 chi ∧
      Fin15AnchoredAtom2992 chi ∧
      Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom3772 chi))))) ∨
      (((((Fin15AnchoredAtom2895 chi ∧
      Fin15AnchoredAtom2898 chi ∧
      Fin15AnchoredAtom2909 chi ∧
      Fin15AnchoredAtom2994 chi ∧
      Fin15AnchoredAtom3279 chi ∧
      Fin15AnchoredAtom3774 chi) ∨
      (Fin15AnchoredAtom2895 chi ∧
      Fin15AnchoredAtom2899 chi ∧
      Fin15AnchoredAtom2910 chi ∧
      Fin15AnchoredAtom2995 chi ∧
      Fin15AnchoredAtom3280 chi ∧
      Fin15AnchoredAtom3775 chi)) ∨
      ((Fin15AnchoredAtom2895 chi ∧
      Fin15AnchoredAtom2900 chi ∧
      Fin15AnchoredAtom2911 chi ∧
      Fin15AnchoredAtom2996 chi ∧
      Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom3776 chi) ∨
      (Fin15AnchoredAtom2896 chi ∧
      Fin15AnchoredAtom2898 chi ∧
      Fin15AnchoredAtom2913 chi ∧
      Fin15AnchoredAtom2998 chi ∧
      Fin15AnchoredAtom3283 chi ∧
      Fin15AnchoredAtom3778 chi))) ∨
      (((Fin15AnchoredAtom2896 chi ∧
      Fin15AnchoredAtom2899 chi ∧
      Fin15AnchoredAtom2914 chi ∧
      Fin15AnchoredAtom2999 chi ∧
      Fin15AnchoredAtom3284 chi ∧
      Fin15AnchoredAtom3779 chi) ∨
      (Fin15AnchoredAtom2896 chi ∧
      Fin15AnchoredAtom2900 chi ∧
      Fin15AnchoredAtom2915 chi ∧
      Fin15AnchoredAtom3000 chi ∧
      Fin15AnchoredAtom3285 chi ∧
      Fin15AnchoredAtom3780 chi)) ∨
      ((Fin15AnchoredAtom2898 chi ∧
      Fin15AnchoredAtom2899 chi ∧
      Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom3004 chi ∧
      Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom3784 chi) ∨
      (Fin15AnchoredAtom2898 chi ∧
      Fin15AnchoredAtom2900 chi ∧
      Fin15AnchoredAtom2920 chi ∧
      Fin15AnchoredAtom3005 chi ∧
      Fin15AnchoredAtom3290 chi ∧
      Fin15AnchoredAtom3785 chi)))) ∨
      ((((Fin15AnchoredAtom2899 chi ∧
      Fin15AnchoredAtom2900 chi ∧
      Fin15AnchoredAtom2921 chi ∧
      Fin15AnchoredAtom3006 chi ∧
      Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom3786 chi) ∨
      (Fin15AnchoredAtom2907 chi ∧
      Fin15AnchoredAtom2909 chi ∧
      Fin15AnchoredAtom2913 chi ∧
      Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom3308 chi ∧
      Fin15AnchoredAtom3803 chi)) ∨
      ((Fin15AnchoredAtom2907 chi ∧
      Fin15AnchoredAtom2910 chi ∧
      Fin15AnchoredAtom2914 chi ∧
      Fin15AnchoredAtom3024 chi ∧
      Fin15AnchoredAtom3309 chi ∧
      Fin15AnchoredAtom3804 chi) ∨
      (Fin15AnchoredAtom2907 chi ∧
      Fin15AnchoredAtom2911 chi ∧
      Fin15AnchoredAtom2915 chi ∧
      Fin15AnchoredAtom3025 chi ∧
      Fin15AnchoredAtom3310 chi ∧
      Fin15AnchoredAtom3805 chi))) ∨
      (((Fin15AnchoredAtom2909 chi ∧
      Fin15AnchoredAtom2910 chi ∧
      Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom3029 chi ∧
      Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom3809 chi) ∨
      (Fin15AnchoredAtom2909 chi ∧
      Fin15AnchoredAtom2911 chi ∧
      Fin15AnchoredAtom2920 chi ∧
      Fin15AnchoredAtom3030 chi ∧
      Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom3810 chi)) ∨
      ((Fin15AnchoredAtom2910 chi ∧
      Fin15AnchoredAtom2911 chi ∧
      Fin15AnchoredAtom2921 chi ∧
      Fin15AnchoredAtom3031 chi ∧
      Fin15AnchoredAtom3316 chi ∧
      Fin15AnchoredAtom3811 chi) ∨
      (Fin15AnchoredAtom2913 chi ∧
      Fin15AnchoredAtom2914 chi ∧
      Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom3035 chi ∧
      Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom3815 chi))))))) ∨
      ((((((Fin15AnchoredAtom2913 chi ∧
      Fin15AnchoredAtom2915 chi ∧
      Fin15AnchoredAtom2920 chi ∧
      Fin15AnchoredAtom3036 chi ∧
      Fin15AnchoredAtom3321 chi ∧
      Fin15AnchoredAtom3816 chi) ∨
      ((Fin15AnchoredAtom2914 chi ∧
      Fin15AnchoredAtom2915 chi ∧
      Fin15AnchoredAtom2921 chi ∧
      Fin15AnchoredAtom3037 chi ∧
      Fin15AnchoredAtom3322 chi ∧
      Fin15AnchoredAtom3817 chi) ∨
      (Fin15AnchoredAtom2916 chi ∧
      Fin15AnchoredAtom2917 chi ∧
      Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom3038 chi ∧
      Fin15AnchoredAtom3323 chi ∧
      Fin15AnchoredAtom3818 chi))) ∨
      (((Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom2920 chi ∧
      Fin15AnchoredAtom2921 chi ∧
      Fin15AnchoredAtom3041 chi ∧
      Fin15AnchoredAtom3326 chi ∧
      Fin15AnchoredAtom3821 chi) ∨
      (Fin15AnchoredAtom2922 chi ∧
      Fin15AnchoredAtom2924 chi ∧
      Fin15AnchoredAtom2931 chi ∧
      Fin15AnchoredAtom2959 chi ∧
      Fin15AnchoredAtom3328 chi ∧
      Fin15AnchoredAtom3823 chi)) ∨
      ((Fin15AnchoredAtom2922 chi ∧
      Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom2932 chi ∧
      Fin15AnchoredAtom2960 chi ∧
      Fin15AnchoredAtom3329 chi ∧
      Fin15AnchoredAtom3824 chi) ∨
      (Fin15AnchoredAtom2922 chi ∧
      Fin15AnchoredAtom2927 chi ∧
      Fin15AnchoredAtom2934 chi ∧
      Fin15AnchoredAtom2962 chi ∧
      Fin15AnchoredAtom3331 chi ∧
      Fin15AnchoredAtom3826 chi)))) ∨
      ((((Fin15AnchoredAtom2922 chi ∧
      Fin15AnchoredAtom2928 chi ∧
      Fin15AnchoredAtom2935 chi ∧
      Fin15AnchoredAtom2963 chi ∧
      Fin15AnchoredAtom3332 chi ∧
      Fin15AnchoredAtom3827 chi) ∨
      (Fin15AnchoredAtom2922 chi ∧
      Fin15AnchoredAtom2929 chi ∧
      Fin15AnchoredAtom2936 chi ∧
      Fin15AnchoredAtom2964 chi ∧
      Fin15AnchoredAtom3333 chi ∧
      Fin15AnchoredAtom3828 chi)) ∨
      ((Fin15AnchoredAtom2923 chi ∧
      Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom2938 chi ∧
      Fin15AnchoredAtom2966 chi ∧
      Fin15AnchoredAtom3335 chi ∧
      Fin15AnchoredAtom3830 chi) ∨
      (Fin15AnchoredAtom2924 chi ∧
      Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom2943 chi ∧
      Fin15AnchoredAtom2971 chi ∧
      Fin15AnchoredAtom3340 chi ∧
      Fin15AnchoredAtom3835 chi))) ∨
      (((Fin15AnchoredAtom2924 chi ∧
      Fin15AnchoredAtom2927 chi ∧
      Fin15AnchoredAtom2945 chi ∧
      Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom3837 chi) ∨
      (Fin15AnchoredAtom2924 chi ∧
      Fin15AnchoredAtom2928 chi ∧
      Fin15AnchoredAtom2946 chi ∧
      Fin15AnchoredAtom2974 chi ∧
      Fin15AnchoredAtom3343 chi ∧
      Fin15AnchoredAtom3838 chi)) ∨
      ((Fin15AnchoredAtom2924 chi ∧
      Fin15AnchoredAtom2929 chi ∧
      Fin15AnchoredAtom2947 chi ∧
      Fin15AnchoredAtom2975 chi ∧
      Fin15AnchoredAtom3344 chi ∧
      Fin15AnchoredAtom3839 chi) ∨
      (Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom2927 chi ∧
      Fin15AnchoredAtom2949 chi ∧
      Fin15AnchoredAtom2977 chi ∧
      Fin15AnchoredAtom3346 chi ∧
      Fin15AnchoredAtom3841 chi))))) ∨
      (((((Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom2928 chi ∧
      Fin15AnchoredAtom2950 chi ∧
      Fin15AnchoredAtom2978 chi ∧
      Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom3842 chi) ∨
      (Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom2929 chi ∧
      Fin15AnchoredAtom2951 chi ∧
      Fin15AnchoredAtom2979 chi ∧
      Fin15AnchoredAtom3348 chi ∧
      Fin15AnchoredAtom3843 chi)) ∨
      ((Fin15AnchoredAtom2927 chi ∧
      Fin15AnchoredAtom2928 chi ∧
      Fin15AnchoredAtom2955 chi ∧
      Fin15AnchoredAtom2983 chi ∧
      Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom3847 chi) ∨
      (Fin15AnchoredAtom2927 chi ∧
      Fin15AnchoredAtom2929 chi ∧
      Fin15AnchoredAtom2956 chi ∧
      Fin15AnchoredAtom2984 chi ∧
      Fin15AnchoredAtom3353 chi ∧
      Fin15AnchoredAtom3848 chi))) ∨
      (((Fin15AnchoredAtom2928 chi ∧
      Fin15AnchoredAtom2929 chi ∧
      Fin15AnchoredAtom2957 chi ∧
      Fin15AnchoredAtom2985 chi ∧
      Fin15AnchoredAtom3354 chi ∧
      Fin15AnchoredAtom3849 chi) ∨
      (Fin15AnchoredAtom2931 chi ∧
      Fin15AnchoredAtom2932 chi ∧
      Fin15AnchoredAtom2943 chi ∧
      Fin15AnchoredAtom2992 chi ∧
      Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom3856 chi)) ∨
      ((Fin15AnchoredAtom2931 chi ∧
      Fin15AnchoredAtom2934 chi ∧
      Fin15AnchoredAtom2945 chi ∧
      Fin15AnchoredAtom2994 chi ∧
      Fin15AnchoredAtom3363 chi ∧
      Fin15AnchoredAtom3858 chi) ∨
      (Fin15AnchoredAtom2931 chi ∧
      Fin15AnchoredAtom2935 chi ∧
      Fin15AnchoredAtom2946 chi ∧
      Fin15AnchoredAtom2995 chi ∧
      Fin15AnchoredAtom3364 chi ∧
      Fin15AnchoredAtom3859 chi)))) ∨
      ((((Fin15AnchoredAtom2931 chi ∧
      Fin15AnchoredAtom2936 chi ∧
      Fin15AnchoredAtom2947 chi ∧
      Fin15AnchoredAtom2996 chi ∧
      Fin15AnchoredAtom3365 chi ∧
      Fin15AnchoredAtom3860 chi) ∨
      (Fin15AnchoredAtom2932 chi ∧
      Fin15AnchoredAtom2934 chi ∧
      Fin15AnchoredAtom2949 chi ∧
      Fin15AnchoredAtom2998 chi ∧
      Fin15AnchoredAtom3367 chi ∧
      Fin15AnchoredAtom3862 chi)) ∨
      ((Fin15AnchoredAtom2932 chi ∧
      Fin15AnchoredAtom2935 chi ∧
      Fin15AnchoredAtom2950 chi ∧
      Fin15AnchoredAtom2999 chi ∧
      Fin15AnchoredAtom3368 chi ∧
      Fin15AnchoredAtom3863 chi) ∨
      (Fin15AnchoredAtom2932 chi ∧
      Fin15AnchoredAtom2936 chi ∧
      Fin15AnchoredAtom2951 chi ∧
      Fin15AnchoredAtom3000 chi ∧
      Fin15AnchoredAtom3369 chi ∧
      Fin15AnchoredAtom3864 chi))) ∨
      (((Fin15AnchoredAtom2934 chi ∧
      Fin15AnchoredAtom2935 chi ∧
      Fin15AnchoredAtom2955 chi ∧
      Fin15AnchoredAtom3004 chi ∧
      Fin15AnchoredAtom3373 chi ∧
      Fin15AnchoredAtom3868 chi) ∨
      (Fin15AnchoredAtom2934 chi ∧
      Fin15AnchoredAtom2936 chi ∧
      Fin15AnchoredAtom2956 chi ∧
      Fin15AnchoredAtom3005 chi ∧
      Fin15AnchoredAtom3374 chi ∧
      Fin15AnchoredAtom3869 chi)) ∨
      ((Fin15AnchoredAtom2935 chi ∧
      Fin15AnchoredAtom2936 chi ∧
      Fin15AnchoredAtom2957 chi ∧
      Fin15AnchoredAtom3006 chi ∧
      Fin15AnchoredAtom3375 chi ∧
      Fin15AnchoredAtom3870 chi) ∨
      (Fin15AnchoredAtom2943 chi ∧
      Fin15AnchoredAtom2945 chi ∧
      Fin15AnchoredAtom2949 chi ∧
      Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom3392 chi ∧
      Fin15AnchoredAtom3887 chi)))))) ∨
      ((((((Fin15AnchoredAtom2943 chi ∧
      Fin15AnchoredAtom2946 chi ∧
      Fin15AnchoredAtom2950 chi ∧
      Fin15AnchoredAtom3024 chi ∧
      Fin15AnchoredAtom3393 chi ∧
      Fin15AnchoredAtom3888 chi) ∨
      (Fin15AnchoredAtom2943 chi ∧
      Fin15AnchoredAtom2947 chi ∧
      Fin15AnchoredAtom2951 chi ∧
      Fin15AnchoredAtom3025 chi ∧
      Fin15AnchoredAtom3394 chi ∧
      Fin15AnchoredAtom3889 chi)) ∨
      ((Fin15AnchoredAtom2945 chi ∧
      Fin15AnchoredAtom2946 chi ∧
      Fin15AnchoredAtom2955 chi ∧
      Fin15AnchoredAtom3029 chi ∧
      Fin15AnchoredAtom3398 chi ∧
      Fin15AnchoredAtom3893 chi) ∨
      (Fin15AnchoredAtom2945 chi ∧
      Fin15AnchoredAtom2947 chi ∧
      Fin15AnchoredAtom2956 chi ∧
      Fin15AnchoredAtom3030 chi ∧
      Fin15AnchoredAtom3399 chi ∧
      Fin15AnchoredAtom3894 chi))) ∨
      (((Fin15AnchoredAtom2946 chi ∧
      Fin15AnchoredAtom2947 chi ∧
      Fin15AnchoredAtom2957 chi ∧
      Fin15AnchoredAtom3031 chi ∧
      Fin15AnchoredAtom3400 chi ∧
      Fin15AnchoredAtom3895 chi) ∨
      (Fin15AnchoredAtom2949 chi ∧
      Fin15AnchoredAtom2950 chi ∧
      Fin15AnchoredAtom2955 chi ∧
      Fin15AnchoredAtom3035 chi ∧
      Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom3899 chi)) ∨
      ((Fin15AnchoredAtom2949 chi ∧
      Fin15AnchoredAtom2951 chi ∧
      Fin15AnchoredAtom2956 chi ∧
      Fin15AnchoredAtom3036 chi ∧
      Fin15AnchoredAtom3405 chi ∧
      Fin15AnchoredAtom3900 chi) ∨
      (Fin15AnchoredAtom2950 chi ∧
      Fin15AnchoredAtom2951 chi ∧
      Fin15AnchoredAtom2957 chi ∧
      Fin15AnchoredAtom3037 chi ∧
      Fin15AnchoredAtom3406 chi ∧
      Fin15AnchoredAtom3901 chi)))) ∨
      ((((Fin15AnchoredAtom2955 chi ∧
      Fin15AnchoredAtom2956 chi ∧
      Fin15AnchoredAtom2957 chi ∧
      Fin15AnchoredAtom3041 chi ∧
      Fin15AnchoredAtom3410 chi ∧
      Fin15AnchoredAtom3905 chi) ∨
      (Fin15AnchoredAtom2959 chi ∧
      Fin15AnchoredAtom2960 chi ∧
      Fin15AnchoredAtom2971 chi ∧
      Fin15AnchoredAtom2992 chi ∧
      Fin15AnchoredAtom3417 chi ∧
      Fin15AnchoredAtom3912 chi)) ∨
      ((Fin15AnchoredAtom2959 chi ∧
      Fin15AnchoredAtom2962 chi ∧
      Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom2994 chi ∧
      Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom3914 chi) ∨
      (Fin15AnchoredAtom2959 chi ∧
      Fin15AnchoredAtom2963 chi ∧
      Fin15AnchoredAtom2974 chi ∧
      Fin15AnchoredAtom2995 chi ∧
      Fin15AnchoredAtom3420 chi ∧
      Fin15AnchoredAtom3915 chi))) ∨
      (((Fin15AnchoredAtom2959 chi ∧
      Fin15AnchoredAtom2964 chi ∧
      Fin15AnchoredAtom2975 chi ∧
      Fin15AnchoredAtom2996 chi ∧
      Fin15AnchoredAtom3421 chi ∧
      Fin15AnchoredAtom3916 chi) ∨
      (Fin15AnchoredAtom2960 chi ∧
      Fin15AnchoredAtom2962 chi ∧
      Fin15AnchoredAtom2977 chi ∧
      Fin15AnchoredAtom2998 chi ∧
      Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom3918 chi)) ∨
      ((Fin15AnchoredAtom2960 chi ∧
      Fin15AnchoredAtom2963 chi ∧
      Fin15AnchoredAtom2978 chi ∧
      Fin15AnchoredAtom2999 chi ∧
      Fin15AnchoredAtom3424 chi ∧
      Fin15AnchoredAtom3919 chi) ∨
      (Fin15AnchoredAtom2960 chi ∧
      Fin15AnchoredAtom2964 chi ∧
      Fin15AnchoredAtom2979 chi ∧
      Fin15AnchoredAtom3000 chi ∧
      Fin15AnchoredAtom3425 chi ∧
      Fin15AnchoredAtom3920 chi))))) ∨
      (((((Fin15AnchoredAtom2962 chi ∧
      Fin15AnchoredAtom2963 chi ∧
      Fin15AnchoredAtom2983 chi ∧
      Fin15AnchoredAtom3004 chi ∧
      Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom3924 chi) ∨
      (Fin15AnchoredAtom2962 chi ∧
      Fin15AnchoredAtom2964 chi ∧
      Fin15AnchoredAtom2984 chi ∧
      Fin15AnchoredAtom3005 chi ∧
      Fin15AnchoredAtom3430 chi ∧
      Fin15AnchoredAtom3925 chi)) ∨
      ((Fin15AnchoredAtom2963 chi ∧
      Fin15AnchoredAtom2964 chi ∧
      Fin15AnchoredAtom2985 chi ∧
      Fin15AnchoredAtom3006 chi ∧
      Fin15AnchoredAtom3431 chi ∧
      Fin15AnchoredAtom3926 chi) ∨
      (Fin15AnchoredAtom2971 chi ∧
      Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom2977 chi ∧
      Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom3448 chi ∧
      Fin15AnchoredAtom3943 chi))) ∨
      (((Fin15AnchoredAtom2971 chi ∧
      Fin15AnchoredAtom2974 chi ∧
      Fin15AnchoredAtom2978 chi ∧
      Fin15AnchoredAtom3024 chi ∧
      Fin15AnchoredAtom3449 chi ∧
      Fin15AnchoredAtom3944 chi) ∨
      (Fin15AnchoredAtom2971 chi ∧
      Fin15AnchoredAtom2975 chi ∧
      Fin15AnchoredAtom2979 chi ∧
      Fin15AnchoredAtom3025 chi ∧
      Fin15AnchoredAtom3450 chi ∧
      Fin15AnchoredAtom3945 chi)) ∨
      ((Fin15AnchoredAtom2972 chi ∧
      Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom2980 chi ∧
      Fin15AnchoredAtom3026 chi ∧
      Fin15AnchoredAtom3451 chi ∧
      Fin15AnchoredAtom3946 chi) ∨
      (Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom2974 chi ∧
      Fin15AnchoredAtom2983 chi ∧
      Fin15AnchoredAtom3029 chi ∧
      Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom3949 chi)))) ∨
      ((((Fin15AnchoredAtom2973 chi ∧
      Fin15AnchoredAtom2975 chi ∧
      Fin15AnchoredAtom2984 chi ∧
      Fin15AnchoredAtom3030 chi ∧
      Fin15AnchoredAtom3455 chi ∧
      Fin15AnchoredAtom3950 chi) ∨
      (Fin15AnchoredAtom2974 chi ∧
      Fin15AnchoredAtom2975 chi ∧
      Fin15AnchoredAtom2985 chi ∧
      Fin15AnchoredAtom3031 chi ∧
      Fin15AnchoredAtom3456 chi ∧
      Fin15AnchoredAtom3951 chi)) ∨
      ((Fin15AnchoredAtom2977 chi ∧
      Fin15AnchoredAtom2978 chi ∧
      Fin15AnchoredAtom2983 chi ∧
      Fin15AnchoredAtom3035 chi ∧
      Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom3955 chi) ∨
      (Fin15AnchoredAtom2977 chi ∧
      Fin15AnchoredAtom2979 chi ∧
      Fin15AnchoredAtom2984 chi ∧
      Fin15AnchoredAtom3036 chi ∧
      Fin15AnchoredAtom3461 chi ∧
      Fin15AnchoredAtom3956 chi))) ∨
      (((Fin15AnchoredAtom2978 chi ∧
      Fin15AnchoredAtom2979 chi ∧
      Fin15AnchoredAtom2985 chi ∧
      Fin15AnchoredAtom3037 chi ∧
      Fin15AnchoredAtom3462 chi ∧
      Fin15AnchoredAtom3957 chi) ∨
      (Fin15AnchoredAtom2983 chi ∧
      Fin15AnchoredAtom2984 chi ∧
      Fin15AnchoredAtom2985 chi ∧
      Fin15AnchoredAtom3041 chi ∧
      Fin15AnchoredAtom3466 chi ∧
      Fin15AnchoredAtom3961 chi)) ∨
      ((Fin15AnchoredAtom2992 chi ∧
      Fin15AnchoredAtom2994 chi ∧
      Fin15AnchoredAtom2998 chi ∧
      Fin15AnchoredAtom3023 chi ∧
      Fin15AnchoredAtom3483 chi ∧
      Fin15AnchoredAtom3978 chi) ∨
      (Fin15AnchoredAtom2992 chi ∧
      Fin15AnchoredAtom2995 chi ∧
      Fin15AnchoredAtom2999 chi ∧
      Fin15AnchoredAtom3024 chi ∧
      Fin15AnchoredAtom3484 chi ∧
      Fin15AnchoredAtom3979 chi)))))))))) := by
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
                exact fin15Anchored_clause29279 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29280 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29281 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29282 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29283 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29284 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29285 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29286 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29287 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29288 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29289 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29290 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29291 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29292 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29293 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29294 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29295 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29296 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29297 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29298 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29299 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29300 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29301 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29302 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29303 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29304 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29305 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29306 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29307 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29308 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29309 chi hnoStrong hbad
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
                  exact fin15Anchored_clause29310 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29311 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29312 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29313 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29314 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29315 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29316 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29317 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29318 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29319 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29320 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29321 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29322 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29323 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29324 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29325 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29326 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29327 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29328 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29329 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29330 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29331 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29332 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29333 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29334 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29335 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29336 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29337 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29338 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29339 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29340 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29341 chi hnoStrong hbad
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
                exact fin15Anchored_clause29342 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29343 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29344 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29345 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29346 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29347 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29348 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29349 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29350 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29351 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29352 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29353 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29354 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29355 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29356 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29357 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29358 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29359 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29360 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29361 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29362 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29363 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29364 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29365 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29366 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29367 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29368 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29369 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29370 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29371 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29372 chi hnoStrong hbad
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
                  exact fin15Anchored_clause29373 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29374 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29375 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29376 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29377 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29378 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29379 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29380 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29381 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29382 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29383 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29384 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29385 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29386 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29387 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29388 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29389 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29390 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29391 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29392 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29393 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29394 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29395 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29396 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29397 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29398 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29399 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29400 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29401 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29402 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29403 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29404 chi hnoStrong hbad
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
                exact fin15Anchored_clause29405 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29406 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29407 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29408 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29409 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29410 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29411 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29412 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29413 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29414 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29415 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29416 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29417 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29418 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29419 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29420 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29421 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29422 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29423 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29424 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29425 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29426 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29427 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29428 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29429 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29430 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29431 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29432 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29433 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29434 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29435 chi hnoStrong hbad
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
                  exact fin15Anchored_clause29436 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29437 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29438 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29439 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29440 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29441 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29442 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29443 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29444 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29445 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29446 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29447 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29448 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29449 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29450 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29451 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29452 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29453 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29454 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29455 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29456 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29457 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29458 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29459 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29460 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29461 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29462 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29463 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29464 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29465 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29466 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29467 chi hnoStrong hbad
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
                exact fin15Anchored_clause29468 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29469 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29470 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29471 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29472 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29473 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29474 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29475 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29476 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29477 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29478 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29479 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29480 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29481 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29482 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29483 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29484 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29485 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29486 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29487 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29488 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29489 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29490 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29491 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29492 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29493 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29494 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29495 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29496 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29497 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29498 chi hnoStrong hbad
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
                  exact fin15Anchored_clause29499 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29500 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29501 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29502 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29503 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29504 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29505 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29506 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29507 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29508 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29509 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29510 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29511 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29512 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29513 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29514 chi hnoStrong hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29515 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29516 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29517 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29518 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29519 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29520 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29521 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29522 chi hnoStrong hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29523 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29524 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29525 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29526 chi hnoStrong hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29527 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29528 chi hnoStrong hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause29529 chi hnoStrong hbad
                ·
                  exact fin15Anchored_clause29530 chi hnoStrong hbad

end ErdosSzekeres

end
