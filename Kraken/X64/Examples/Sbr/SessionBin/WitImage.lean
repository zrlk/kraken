import Kraken.X64.Examples.Sbr.SessionBin.WitEnvLabs

/-!
# The witness image: distinct labels and `SessPlaced`

The image `WitEnv.img` is well formed (`img_wf`: its labels are distinct) and every text of it
is placed under `wCE`; hence `SessPlaced` (`wPlaced`), with the layout facts (`lcpi`, `labs`,
`jt`) read off the label addresses.

`decide` on `List.Nodup` of the image's ~2000 label keys runs out of memory, and `String.toList`
is the expensive part in the kernel: the keys are read from the UTF-8 bytes (`bkey`) and checked
by a merge sort by fuel (`msort`), a permutation of its input, so a strictly increasing result
shows the keys are distinct.
-/

open Kraken Kraken.X64.Parser
open Kraken.Examples.Sbr.Apply (labelList labelList_nodup)

namespace Kraken.Examples.Sbr.WitEnv

/-! ## Distinct keys by a kernel-evaluable merge sort

`decide` on `List.Nodup` of the ~2000 label keys is quadratic and runs out of memory, and
`List.mergeSort` does not reduce in the kernel (well-founded recursion). `msort` is a merge
sort by fuel; it is a permutation of its input whatever the fuel, so a strictly increasing
result shows the input has no duplicates. -/

/-- Merge, with fuel. -/
def mergeF : Nat → List Nat → List Nat → List Nat
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | n + 1, x :: xs, y :: ys =>
    if x ≤ y then x :: mergeF n xs (y :: ys) else y :: mergeF n (x :: xs) ys

theorem mergeF_perm : ∀ n xs ys, (mergeF n xs ys).Perm (xs ++ ys)
  | 0, _, _ => List.Perm.refl _
  | _ + 1, [], _ => List.Perm.refl _
  | _ + 1, _ :: _, [] => by simp [mergeF]
  | n + 1, x :: xs, y :: ys => by
    unfold mergeF
    split
    · exact (mergeF_perm n xs (y :: ys)).cons x
    · refine ((mergeF_perm n (x :: xs) ys).cons y).trans ?_
      exact (List.perm_middle).symm

/-- Split into the elements at even and at odd positions. -/
def halve : List Nat → List Nat × List Nat
  | [] => ([], [])
  | [a] => ([a], [])
  | a :: b :: t => ((halve t).1.cons a, (halve t).2.cons b)

theorem halve_perm : ∀ l, ((halve l).1 ++ (halve l).2).Perm l
  | [] => List.Perm.refl _
  | [_] => List.Perm.refl _
  | a :: b :: t => by
    have ih := halve_perm t
    simp only [halve, List.cons_append]
    refine List.Perm.cons a ?_
    exact List.perm_middle.trans (ih.cons b)

/-- Merge sort, with fuel. -/
def msort : Nat → List Nat → List Nat
  | 0, l => l
  | n + 1, l => mergeF l.length (msort n (halve l).1) (msort n (halve l).2)

theorem msort_perm : ∀ n l, (msort n l).Perm l
  | 0, _ => List.Perm.refl _
  | n + 1, l => by
    unfold msort
    exact (mergeF_perm _ _ _).trans
      (((msort_perm n _).append (msort_perm n _)).trans (halve_perm l))

/-- Strictly increasing. -/
def strictB : List Nat → Bool
  | a :: b :: t => decide (a < b) && strictB (b :: t)
  | _ => true

theorem strictB_lt : ∀ {a : Nat} {t : List Nat}, strictB (a :: t) = true → ∀ x ∈ t, a < x
  | _, [], _, x, hx => by simp at hx
  | a, b :: t, h, x, hx => by
    simp only [strictB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (strictB_lt h.2 x hx)

theorem strictB_nodup : ∀ {l : List Nat}, strictB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [_], _ => List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  | a :: b :: t, h => by
    refine List.nodup_cons.mpr ⟨fun hm => Nat.lt_irrefl a (strictB_lt h a hm), ?_⟩
    simp only [strictB, Bool.and_eq_true] at h
    exact strictB_nodup h.2

theorem nodup_of_msort {l : List Nat} (n : Nat) (h : strictB (msort n l) = true) : l.Nodup :=
  (msort_perm n l).nodup_iff.mp (strictB_nodup h)

/-- A label's key, from its UTF-8 bytes (cheap in the kernel, unlike `String.toList`). -/
def bkey (s : String) : Nat := s.toUTF8.data.toList.foldl (fun n b => n * 256 + b.toNat) 0

theorem other_entry : ∀ t ∈ otherT, (Program.view t).1 = [] := by decide +kernel

theorem texts_entry : ∀ t ∈ texts, (Program.view t).1 = [] := by
  intro t ht
  simp only [texts, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | rfl
  · exact other_entry t ht
  · rw [@Kraken.Examples.Sbr.Apply.view_body Witness.wCE]

/-- The labels of all texts but `ff_aac_sbr_apply`. -/
def otherLabels : List Label := otherT.flatMap Program.labels

theorem labels_img : Program.labels img = otherLabels ++ labelList := by
  rw [img, Program.labels_flatten, texts, List.flatMap_append, otherLabels]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [@Kraken.Examples.Sbr.Apply.labels_body Witness.wCE]

theorem keys_nodup : ((otherLabels ++ labelList).map bkey).Nodup :=
  nodup_of_msort 12 (by decide +kernel)

theorem img_wf : Program.WF img :=
  ⟨labels_img ▸ (List.pairwise_map.mp keys_nodup).imp fun h e => h (congrArg bkey e)⟩

section
attribute [local instance] wLayout wCE

theorem img_placed : Program.Placed img "LCPI14_0" := by
  obtain ⟨tl, h⟩ : ∃ tl, img = .label "LCPI14_0" :: tl :=
    List.head?_eq_some_iff.mp (show img.head? = some (.label "LCPI14_0") by decide +kernel)
  exact Program.placed_of_layout img_wf h (by decide +kernel)

/-- A text of the image is placed. -/
theorem placedIn_of_mem {p : Program} (hp : p ∈ texts) : Program.PlacedIn p :=
  Program.PlacedIn.of_flatten img_placed.toPlacedIn img_wf.nodup texts_entry hp

/-- The `i`-th text is placed (by its index: no comparison of texts). -/
theorem placed_at (i : Nat) (h : i < texts.length) : Program.PlacedIn texts[i] :=
  placedIn_of_mem (List.getElem_mem h)

/-- `labAt` with the side conditions checked by the kernel. -/
macro "lab_at" l:str n:num : term =>
  `(labAt $l $n (by decide +kernel) (by decide +kernel))

theorem wJtC : Grid.JtC := by
  unfold Grid.JtC Grid.jtOff Grid.JT
  rw [wlab_read_sbr_grid_jt, lab_at "read_sbr_grid.L448b" 184,
    lab_at "read_sbr_grid.L4773" 417, lab_at "read_sbr_grid.L44e3" 210,
    lab_at "read_sbr_grid.L46a2" 351]
  decide +kernel

theorem wLabs : isAligned 16 (lab "LCPI14_1") = true ∧ isAligned 16 (lab "LCPI14_2") = true
    ∧ isAligned 16 (lab "LCPI14_8") = true ∧ isAligned 32 (lab "sbr_qmf_window_ds") = true
    ∧ isAligned 16 (lab "ff_ps_neg") = true ∧ isAligned 16 (lab "ps_mask") = true
    ∧ isAligned 32 (lab "sbr_qmf_window_us") = true ∧ isAligned 16 (lab "ps_mask2") = true
    ∧ isAligned 16 (lab "ps_mask3") = true ∧ isAligned 16 (lab "ps_noise0") = true
    ∧ isAligned 16 (lab "ps_noise13") = true ∧ isAligned 16 (lab "ps_noise2") = true
    ∧ isAligned 32 (lab "pd_reverse") = true := by
  rw [wlab_LCPI14_1, wlab_LCPI14_2, wlab_LCPI14_8, wlab_sbr_qmf_window_ds, wlab_ff_ps_neg,
    wlab_ps_mask, wlab_sbr_qmf_window_us, wlab_ps_mask2, wlab_ps_mask3, wlab_ps_noise0,
    wlab_ps_noise13, wlab_ps_noise2, wlab_pd_reverse]
  decide +kernel

/-- **The binary**: every text of `SessPlaced` is placed, with the layout facts. -/
theorem wPlaced : SessionBin.SessPlaced where
  apply :=
    { apply := placed_at 119 (by decide)
      lfGen := placed_at 82 (by decide)
      hfInv := placed_at 83 (by decide)
      xGen := placed_at 84 (by decide)
      hfAsm := placed_at 85 (by decide)
      qmfSyn := placed_at 86 (by decide)
      dsp := ⟨placed_at 87 (by decide), placed_at 88 (by decide), placed_at 89 (by decide),
        placed_at 90 (by decide), placed_at 91 (by decide), placed_at 92 (by decide),
        placed_at 93 (by decide), placed_at 94 (by decide), placed_at 95 (by decide),
        placed_at 96 (by decide), placed_at 97 (by decide), placed_at 98 (by decide)⟩
      fdsp := ⟨placed_at 99 (by decide), placed_at 100 (by decide), placed_at 101 (by decide),
        placed_at 102 (by decide), placed_at 103 (by decide), placed_at 104 (by decide),
        placed_at 105 (by decide), placed_at 106 (by decide)⟩ }
  grid := placed_at 69 (by decide)
  decExt := placed_at 70 (by decide)
  usac := placed_at 71 (by decide)
  config := placed_at 72 (by decide)
  hdr := placed_at 73 (by decide)
  reset := placed_at 74 (by decide)
  tlim := placed_at 75 (by decide)
  dtdf := placed_at 76 (by decide)
  invf := placed_at 77 (by decide)
  env := placed_at 78 (by decide)
  noise := placed_at 79 (by decide)
  ps := placed_at 80 (by decide)
  init := placed_at 81 (by decide)
  lcpi := by rw [wlab_LCPI5_6]; decide +kernel
  labs := wLabs
  jt := wJtC

/-! ## The stand-ins are placed -/

theorem pl_avLog : Program.PlacedIn avLogT := placed_at 107 (by decide)
theorem pl_avReq : Program.PlacedIn avReqT := placed_at 108 (by decide)
theorem pl_psdsp : Program.PlacedIn psdspT := placed_at 109 (by decide)
theorem pl_psApply : Program.PlacedIn psApplyT := placed_at 110 (by decide)
theorem pl_txFn : Program.PlacedIn txFnT := placed_at 111 (by decide)
theorem pl_powf : Program.PlacedIn powfT := placed_at 112 (by decide)
theorem pl_log2f : Program.PlacedIn log2fT := placed_at 113 (by decide)
theorem pl_txInit : Program.PlacedIn txInitT := placed_at 114 (by decide)
theorem pl_mallocz : Program.PlacedIn malloczT := placed_at 115 (by decide)
theorem pl_memcpy : Program.PlacedIn memcpyT := placed_at 116 (by decide)
theorem pl_memset : Program.PlacedIn memsetT := placed_at 117 (by decide)
theorem pl_sbrdsp : Program.PlacedIn sbrdspT := placed_at 118 (by decide)

end

end Kraken.Examples.Sbr.WitEnv
