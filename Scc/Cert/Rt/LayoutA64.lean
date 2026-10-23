import Spike.Lib.A64Block
import Kraken.Promising.Lower.CodeSegA64Syms
import Scc.Cert.PlaceSyms

/-!
# Code at labels of an emitted AArch64 program

The proofs of runtime routines and compiled functions take their code as
hypotheses: each block at its node's pc (`Spike.Lib.A64.CodeAt`), and
labels at fixed distances from each other. This file discharges them for a
laid-out program from checks on the directive list alone, decided by
evaluation (`decide +kernel`) once per program:

- `blockAt prog l k b`: `b` is the run of instructions starting `k`
  instructions after the first `label l` of `prog`, before any further
  label; `codeAt_blockAt` gives `CodeAt st (label l + 4k) b` in any state
  whose executable lays out `prog`;
- `labelGap prog a b n`: the first `label b` follows the first `label a`
  after exactly `n` instructions; `label_labelGap` gives
  `label b = label a + 4n`.

The layout is any `ValidLayout` executable whose cells begin with `prog`'s
directives, no later cell an instruction (`Lays exe prog`), with the end
address at the end of `prog`'s cells (`endOf exe prog`): the sizes, the start
address and the data directives elsewhere in the program do not matter. An
executable of `prog` alone is one (`Lays.of_eq`, `endOf_of_eq`); so is the
canonical loader's thread, which places label cells for the data symbols
after the code (`lays_threadAt`, `endPc_threadAt`). The checks scan `prog`
up to the label once per block (linear in the program; no whole-program
size computation).
-/

namespace Scc.Cert.Rt.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64

/-- An instruction (not a label, not data). -/
def isIns : Directive → Bool
  | .instr _ => true
  | _ => false

/-- The index of the first `label l`. -/
def labelIdx : List Directive → Label → Option Nat
  | [], _ => none
  | d :: ds, l => if d = .label l then some 0 else (labelIdx ds l).map (· + 1)

/-- The instructions after the first `label l`, up to the next label or data. -/
def run (prog : List Directive) (l : Label) : List Directive :=
  match labelIdx prog l with
  | some n => (prog.drop (n + 1)).takeWhile isIns
  | none => []

/-- `b` is the run after `label l` from its `k`-th instruction on (a prefix). -/
def blockAt (prog : List Directive) (l : Label) (k : Nat) (b : List Directive) : Bool :=
  (labelIdx prog l).isSome && decide (((run prog l).drop k).take b.length = b)

/-- The first `label b` follows the first `label a` after exactly `n`
instructions. -/
def labelGap (prog : List Directive) (a b : Label) (n : Nat) : Bool :=
  match labelIdx prog a, labelIdx prog b with
  | some i, some j => j == i + 1 + n && ((prog.drop (i + 1)).take n).all isIns
  | _, _ => false

theorem labelIdx_spec : ∀ {prog : List Directive} {l : Label} {n : Nat}, labelIdx prog l = some n →
    prog[n]? = some (.label l) ∧ ∀ d ∈ prog.take n, d ≠ .label l
  | [], _, _, h => by simp [labelIdx] at h
  | d :: ds, l, n, h => by
    unfold labelIdx at h
    split at h
    · cases h; simp_all
    · obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨h1, h2⟩ := labelIdx_spec hm
      refine ⟨by simpa using h1, ?_⟩
      intro d' hd'
      rw [List.take_succ_cons, List.mem_cons] at hd'
      rcases hd' with rfl | hd'
      · assumption
      · exact h2 d' hd'

/-! ## Layouts of a program -/

/-- **`exe` lays out `prog`**: its cells begin with `prog`'s directives (any
sizes), and no later cell is an instruction (the canonical loader's label
and padding cells for the data symbols, `Scc.Sem.A64.threadAt`). -/
structure Lays (exe : Executable) (prog : List Directive) : Prop where
  pre : (exe.2.take prog.length).map (·.1) = prog
  rest : ∀ c ∈ exe.2.drop prog.length, ∀ i, c.1 ≠ .instr i

/-- The end of `prog`'s cells in `exe`: where a thread running `prog` halts. -/
def endOf (exe : Executable) (prog : List Directive) : Int64 :=
  exe.1 + .ofNat ((exe.2.take prog.length).map (·.2)).sum

/-- An executable of `prog` alone lays it out. -/
theorem Lays.of_eq {exe : Executable} {prog : List Directive} (hp : exe.2.map (·.1) = prog) : Lays exe prog where
  pre := by rw [← hp, List.length_map, List.take_length]
  rest := by intro c hc; rw [← hp, List.length_map, List.drop_length] at hc; simp at hc

/-- In an executable of `prog` alone, `prog` ends at the end of the cells. -/
theorem endOf_of_eq {exe : Executable} {prog : List Directive} (hp : exe.2.map (·.1) = prog) :
    endOf exe prog = exe.1 + .ofNat (exe.2.map (·.2)).sum := by
  rw [endOf, ← hp, List.length_map, List.take_length]

/-- The first `n ≤ prog.length` cells are `prog`'s first `n` directives. -/
theorem Lays.take_fst {exe : Executable} {prog : List Directive} (hp : Lays exe prog) {n : Nat}
    (hn : n ≤ prog.length) : (exe.2.take n).map (·.1) = prog.take n := by
  conv => rhs; rw [← hp.pre]
  rw [List.map_take, List.map_take, List.take_take, Nat.min_eq_left hn]

/-- The directives of the cells: `prog`, then no instruction. -/
theorem Lays.fst_eq {exe : Executable} {prog : List Directive} (hp : Lays exe prog) :
    exe.2.map (·.1) = prog ++ (exe.2.drop prog.length).map (·.1) := by
  conv => lhs; rw [← List.take_append_drop prog.length exe.2]
  rw [List.map_append, hp.pre]

/-- The executable's view of the directive list. -/
theorem getElem?_fst {exe : Executable} {prog : List Directive} (hp : Lays exe prog) {n : Nat}
    {d : Directive} (h : prog[n]? = some d) : ∃ z, exe.2[n]? = some (d, z) := by
  have hn : n < prog.length := by
    rcases Nat.lt_or_ge n prog.length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at h; cases h
  have h' : (exe.2.map (·.1))[n]? = some d := by
    rw [hp.fst_eq, List.getElem?_append_left hn, h]
  rw [List.getElem?_map] at h'
  cases hx : exe.2[n]? with
  | none => rw [hx] at h'; cases h'
  | some x => rw [hx] at h'; exact ⟨x.2, by cases h'; rfl⟩

/-- No cell of `exe` after `prog`'s is an instruction. -/
theorem takeWhile_append_noIns : ∀ (a t : List Directive), (∀ d ∈ t, isIns d = false) →
    (a ++ t).takeWhile isIns = a.takeWhile isIns
  | [], [], _ => rfl
  | [], d :: t, h => by simp [h d (List.mem_cons_self ..)]
  | x :: a, t, h => by
    by_cases hx : isIns x = true
    · simp only [List.cons_append, List.takeWhile_cons, hx, ↓reduceIte]
      rw [takeWhile_append_noIns a t h]
    · simp [hx]

/-- A run of instructions in the executable: the cells of the instructions
at the head of the list, each of 4 bytes, then the rest. -/
theorem split_run : ∀ (L : List (Directive × Nat)), (∀ c ∈ L, isIns c.1 = true → c.2 = 4) →
    L = ((L.map (·.1)).takeWhile isIns).map (·, 4) ++ L.dropWhile (fun c => isIns c.1)
  | [], _ => rfl
  | (d, z) :: L, h => by
    by_cases hd : isIns d = true
    · have hz : z = 4 := h (d, z) (List.mem_cons_self ..) hd
      subst hz
      simp only [List.map_cons, List.takeWhile_cons, hd, List.dropWhile_cons, ite_true, List.cons_append]
      exact congrArg _ (split_run L fun c hc => h c (List.mem_cons_of_mem _ hc))
    · simp [hd]

theorem mem_takeWhile {p : Directive → Bool} : ∀ {l : List Directive} {d : Directive},
    d ∈ l.takeWhile p → p d = true
  | [], _, h => by simp at h
  | x :: l, d, h => by
    by_cases hx : p x = true
    · simp only [List.takeWhile_cons, hx, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | h
      · exact hx
      · exact mem_takeWhile h
    · simp [hx] at h

theorem isLabel_of_isIns {d : Directive} (h : isIns d = true) : d.isLabel = false := by
  cases d <;> simp_all [isIns, Directive.isLabel]

/-- **A run of instructions at `pc`** in a layout of `prog` is code there
(`CodeAt.of_codeAt` with the end address at the end of `prog`'s cells). -/
theorem codeAt_of_lays {st : State} [hv : Executable.ValidLayout st.exe] {prog : List Directive}
    (hp : Lays st.exe prog) (hend : st.endPc = endOf st.exe prog) {pc : Int64} {ds : List Directive}
    {rest : List (Directive × Nat)} (h : Kraken.Executable.codeAt st.exe pc = ds.map (·, 4) ++ rest)
    (hds : ∀ d ∈ ds, isIns d = true) : CodeAt st pc ds := by
  intro j d hd
  have hj : j < ds.length := by
    rcases Nat.lt_or_ge j ds.length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at hd; cases hd
  have hseg := Kraken.Executable.codeAt_segment4 st.exe h (fun d hd => isLabel_of_isIns (hds d hd)) j hj
  have hdj : ds[j] = d := by rw [List.getElem?_eq_getElem hj] at hd; exact Option.some.inj hd
  rw [List.drop_eq_getElem_cons hj, List.map_cons, List.cons_append, hdj] at hseg
  have hi := hds d (hdj ▸ List.getElem_mem hj)
  cases d with
  | instr i =>
    exact Kraken.Promising.Lower.A64.cellAt_of_codeAt_instr (st := { st with st := (st.st.1, pc + .ofNat (4 * j)) })
      hv (List.take_append_drop prog.length st.exe.2).symm hp.rest hend hseg
  | _ => simp [isIns] at hi

/-- **The run after a label is code there.** -/
theorem codeAt_run {exe : Executable} [hv : Executable.ValidLayout exe] {prog : List Directive}
    (hp : Lays exe prog) {st : State} (he : st.exe = exe)
    (hend : st.endPc = endOf exe prog) {l : Label} (hl : (labelIdx prog l).isSome) :
    CodeAt st ((_root_.Executable.labels exe).label l) (run prog l) := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨hpn, hfirst⟩ := labelIdx_spec hn
  obtain ⟨z, hz⟩ := getElem?_fst hp hpn
  have hnl : n < prog.length := by
    rcases Nat.lt_or_ge n prog.length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at hpn; cases hpn
  have hfirst' : ∀ dz ∈ exe.2.take n, dz.1 ≠ Directive.label l := by
    intro dz hdz
    apply hfirst
    rw [← hp.take_fst (Nat.le_of_lt hnl)]
    exact List.mem_map_of_mem hdz
  have hcode := Kraken.Executable.codeAt_label exe hz hfirst'
  simp only [run, hn]
  -- the cells after the label: the run, 4 bytes each, then the rest
  have h4 : ∀ c ∈ exe.2.drop (n + 1), isIns c.1 = true → c.2 = 4 := by
    intro c hc hi
    obtain ⟨i, hi'⟩ := List.getElem?_of_mem hc
    rw [List.getElem?_drop] at hi'
    obtain ⟨d, z⟩ := c
    cases d with
    | instr ins => exact hv.instr_size _ ins z hi'
    | _ => simp [isIns] at hi
  have hsplit := split_run _ h4
  rw [List.map_drop, hp.fst_eq, List.drop_append_of_le_length (by omega),
    takeWhile_append_noIns _ _ (fun d hd => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
      cases hc1 : c.1 with
      | instr i => exact absurd hc1 (hp.rest c hc i)
      | _ => rfl)] at hsplit
  generalize hR : (prog.drop (n + 1)).takeWhile isIns = R at hsplit ⊢
  have hRi : ∀ d ∈ R, isIns d = true := by
    rw [← hR]; intro d hd; exact mem_takeWhile hd
  cases R with
  | nil => intro j d hd; simp at hd
  | cons d R' =>
    have hdl : d.isLabel = false := isLabel_of_isIns (hRi d (List.mem_cons_self ..))
    rw [hsplit] at hcode
    simp only [List.map_cons, List.cons_append, List.dropWhile_cons, hdl] at hcode
    subst he
    refine codeAt_of_lays hp hend (rest := st.exe.2.drop (n + 1) |>.dropWhile (fun c => isIns c.1)) ?_
      hRi
    simpa using hcode

/-- **A block of the run after a label is code at its address.** -/
theorem codeAt_blockAt {exe : Executable} [Executable.ValidLayout exe] {prog : List Directive}
    (hp : Lays exe prog) {st : State} (he : st.exe = exe)
    (hend : st.endPc = endOf exe prog) {l : Label} {k : Nat} {b : List Directive}
    (h : blockAt prog l k b = true) :
    CodeAt st ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)) b := by
  simp only [blockAt, Bool.and_eq_true, decide_eq_true_eq] at h
  have := ((codeAt_run hp he hend h.1).drop k).take b.length
  rwa [h.2] at this

/-- **The distance between two labels.** -/
theorem label_labelGap {exe : Executable} [hv : Executable.ValidLayout exe] {prog : List Directive}
    (hp : Lays exe prog) {a b : Label} {n : Nat} (h : labelGap prog a b n = true) :
    (_root_.Executable.labels exe).label b = (_root_.Executable.labels exe).label a + Int64.ofNat (4 * n) := by
  unfold labelGap at h
  split at h
  next i j hi hj =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨rfl, hins⟩ := h
    obtain ⟨hpi, hfi⟩ := labelIdx_spec hi
    obtain ⟨hpj, hfj⟩ := labelIdx_spec hj
    obtain ⟨zi, hzi⟩ := getElem?_fst hp hpi
    obtain ⟨zj, hzj⟩ := getElem?_fst hp hpj
    have hzi0 := hv.label_size i a zi hzi
    have hzj0 := hv.label_size _ b zj hzj
    subst hzi0 hzj0
    have first (l : Label) (m : Nat) (hm : m ≤ prog.length) (hf : ∀ d ∈ prog.take m, d ≠ .label l) :
        ∀ dz ∈ exe.2.take m, dz.1 ≠ Directive.label l := by
      intro dz hdz
      apply hf
      rw [← hp.take_fst hm]
      exact List.mem_map_of_mem hdz
    have hlen (k : Nat) (l : Label) (h : prog[k]? = some (.label l)) : k ≤ prog.length := by
      rcases Nat.lt_or_ge k prog.length with hc | hc
      · exact Nat.le_of_lt hc
      · rw [List.getElem?_eq_none hc] at h; cases h
    rw [Kraken.Executable.label_addrOf exe a i hzi (first a i (hlen _ _ hpi) hfi),
      Kraken.Executable.label_addrOf exe b _ hzj (first b _ (hlen _ _ hpj) hfj)]
    -- past the label (0 bytes), then `m` instructions (4 bytes each)
    have step : ∀ m, m ≤ n → Kraken.Executable.addrOf exe (i + 1 + m) = Kraken.Executable.addrOf exe i + Int64.ofNat (4 * m) := by
      intro m
      induction m with
      | zero => intro _; simpa using Kraken.Executable.addrOf_succ exe hzi
      | succ m ih =>
        intro hm
        have hpm : prog[i + 1 + m]? ∈ ((prog.drop (i + 1)).take n).map some := by
          rw [show i + 1 + m = (i + 1) + m by omega, ← List.getElem?_drop]
          have hlt : m < ((prog.drop (i + 1)).take n).length := by
            have : i + 1 + n < prog.length := by
              rcases Nat.lt_or_ge (i + 1 + n) prog.length with hc | hc
              · exact hc
              · rw [List.getElem?_eq_none hc] at hpj; cases hpj
            simp; omega
          rw [show (prog.drop (i + 1))[m]? = ((prog.drop (i + 1)).take n)[m]? by
            rw [List.getElem?_take_of_lt (by omega)], List.getElem?_eq_getElem hlt]
          exact List.mem_map_of_mem (List.getElem_mem hlt)
        obtain ⟨d, hd, hdm⟩ := List.mem_map.mp hpm
        obtain ⟨z, hz⟩ := getElem?_fst hp hdm.symm
        have hdi := hins d hd
        cases d with
        | instr ins =>
          have hz4 := hv.instr_size _ ins z hz
          subst hz4
          rw [show i + 1 + (m + 1) = (i + 1 + m) + 1 by omega, Kraken.Executable.addrOf_succ exe hz,
            ih (by omega), Int64.add_assoc, ← Int64.ofNat_add, show 4 * (m + 1) = 4 * m + 4 by omega]
        | _ => simp [isIns] at hdi
    exact step n (Nat.le_refl n)
  next => simp at h

/-! ## The canonical loader's thread -/

section Loaded

open Scc.Sem Scc.Sem.A64

/-- The label and padding cells `placeSyms` appends hold no instruction. -/
theorem placeSyms_noIns (cur : Nat) (syms : List (String × Nat)) :
    ∀ c ∈ placeSyms (Directive.byteArray (.mk #[])) Directive.label cur syms, ∀ i, c.1 ≠ .instr i := by
  intro c hc i
  rcases (PlaceSyms.placeSyms_spec _ _ cur syms).1 c hc with ⟨h, -⟩ | ⟨p, -, rfl⟩
  · rw [h]; simp
  · simp

/-- **The canonical loader's thread with no data symbol below the code**:
the executable starts at the code, the program's cells first, then the
label and padding cells of the data symbols (`Scc.Sem.A64.threadAt`; no
cells before the code, `PlaceSyms.placeBelow_of_above`). -/
theorem threadAt_exe_of_above {E : Entry} {base : Nat} {prog : Program} {syms : List (String × Nat)}
    (h : ∀ p ∈ syms, base ≤ p.2) :
    (threadAt E base prog syms).exe = (Int64.ofNat base, prog.map (fun d => (d, d.fakeSize)) ++
      placeSyms (.byteArray (.mk #[])) .label (codeEnd base prog) syms) := by
  simp only [threadAt, PlaceSyms.exeStart_of_above h, PlaceSyms.placeBelow_of_above _ _ h,
    PlaceSyms.symsFrom_of_above h, List.nil_append]

/-- **The canonical loader's thread is the old-layout one** when every data
symbol lies above the end of the code at distinct addresses (`symsOk`): the
executable at the code, the program's cells, then the old `placeSyms`
(`PlaceSyms.placeSymsOld`: a padding cell before each label cell). -/
theorem threadAt_exe_eq_old {E : Entry} {base : Nat} {prog : Program} {syms : List (String × Nat)}
    (h : ∀ p ∈ syms, codeEnd base prog < p.2) (hnd : (syms.map (·.2)).Nodup) :
    (threadAt E base prog syms).exe = (Int64.ofNat base, prog.map (fun d => (d, d.fakeSize)) ++
      PlaceSyms.placeSymsOld (.byteArray (.mk #[])) .label (codeEnd base prog) syms) := by
  rw [threadAt_exe_of_above (fun p hp => by have := h p hp; simp only [codeEnd] at this; omega),
    PlaceSyms.placeSyms_eq_old _ _ h hnd]

/-- **The canonical loader's thread lays out its program**
(`Scc.Sem.A64.threadAt`): the program's cells, then label and padding cells
for the data symbols. With `endPc_threadAt` and a valid layout
(`validLayout_threadAt`), the hypotheses of `codeAt_blockAt`,
`label_labelGap` and every theorem built on them, for the loaded state and
every state a run reaches from it (a step keeps the executable and the end
address). -/
theorem lays_threadAt (E : Entry) (base : Nat) (prog : Program) (syms : List (String × Nat))
    (h : ∀ p ∈ syms, base ≤ p.2) : Lays (threadAt E base prog syms).exe prog where
  pre := by rw [threadAt_exe_of_above h]; simp [Function.comp_def]
  rest := by
    rw [threadAt_exe_of_above h]
    simp only [List.drop_left' (List.length_map _)]
    exact placeSyms_noIns _ _

/-- **The canonical loader's thread halts at the end of its program.** -/
theorem endPc_threadAt (E : Entry) (base : Nat) (prog : Program) (syms : List (String × Nat))
    (h : ∀ p ∈ syms, base ≤ p.2) :
    (threadAt E base prog syms).endPc = endOf (threadAt E base prog syms).exe prog := by
  rw [threadAt_exe_of_above h]
  simp only [threadAt, endOf, codeEnd, List.take_left' (List.length_map _), List.map_map]
  rw [Int64.ofNat_add]
  rfl

/-- A dormant slot has the loaded thread's executable and end address. -/
theorem dormantAt_exe (E : Entry) (base : Nat) (prog : Program) (syms : List (String × Nat)) :
    (dormantAt E base prog syms).exe = (threadAt E base prog syms).exe ∧
      (dormantAt E base prog syms).endPc = (threadAt E base prog syms).endPc := ⟨rfl, rfl⟩

/-- The step of `placeSyms`' fold. -/
private def placeStep (acc : List (Directive × Nat) × Nat) (xa : String × Nat) : List (Directive × Nat) × Nat :=
  (acc.1 ++ [((Directive.byteArray (.mk #[]) : Directive), xa.2 - acc.2), (.label xa.1, 0)], max xa.2 acc.2)

/-- `placeSyms`' fold over symbols in strictly increasing address order, all
above the current address `c` and below `B`: it appends valid cells
(non-empty padding, empty labels) whose sizes take `c` to its new current
address, below `B`. -/
private theorem placeStep_fold : ∀ (L : List (String × Nat)) (cells : List (Directive × Nat)) (c B : Nat),
    (∀ p ∈ L, c < p.2 ∧ p.2 < B) → L.Pairwise (fun a b => a.2 < b.2) → c < B →
    ∃ new, (L.foldl placeStep (cells, c)).1 = cells ++ new ∧ (∀ x ∈ new, Kraken.Executable.cellOk x = true) ∧
      (new.map (·.2)).sum + c = (L.foldl placeStep (cells, c)).2 ∧ (L.foldl placeStep (cells, c)).2 < B
  | [], cells, c, _, _, _, hc => ⟨[], by simp, by simp, by simp, hc⟩
  | (x, a) :: L, cells, c, B, hL, hp, _ => by
    have ha := hL (x, a) (List.mem_cons_self ..)
    have hp' := List.pairwise_cons.mp hp
    obtain ⟨new, h1, h2, h3, h4⟩ := placeStep_fold L
      (cells ++ [((Directive.byteArray (.mk #[]) : Directive), a - c), (.label x, 0)]) a B
      (fun p hp => ⟨hp'.1 p hp, (hL p (List.mem_cons_of_mem _ hp)).2⟩) hp'.2 ha.2
    have hmax : max a c = a := Nat.max_eq_left (Nat.le_of_lt ha.1)
    refine ⟨[((Directive.byteArray (.mk #[]) : Directive), a - c), (.label x, 0)] ++ new, ?_, ?_, ?_, ?_⟩
    · simp only [List.foldl_cons, placeStep, hmax]; rw [h1, List.append_assoc]
    · intro y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with (rfl | rfl) | hy
      · simp [Kraken.Executable.cellOk]; omega
      · simp [Kraken.Executable.cellOk]
      · exact h2 y hy
    · simp only [List.foldl_cons, placeStep, hmax] at h3 ⊢
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
      omega
    · simpa only [List.foldl_cons, placeStep, hmax] using h4

/-- **The data symbols the canonical loader can place**: each above the end
of the code and below `base + 2⁶⁴`, at distinct addresses, the code fitting
the address space (no padding cell is empty and the cells fit,
`validLayout_threadAt`). -/
def symsOk (base : Nat) (prog : Program) (syms : List (String × Nat)) : Bool :=
  decide ((prog.map Directive.fakeSize).sum < 2 ^ 64) &&
  syms.all (fun p => decide (codeEnd base prog < p.2) && decide (p.2 < base + 2 ^ 64)) &&
  decide (syms.map (·.2)).Nodup

/-- The data symbols `symsOk` passes are above the end of the code. -/
theorem codeEnd_lt_of_symsOk {base : Nat} {prog : Program} {syms : List (String × Nat)}
    (h : symsOk base prog syms = true) : ∀ p ∈ syms, codeEnd base prog < p.2 := fun p hp => by
  simp only [symsOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact (h.1.2 p hp).1

/-- The data symbols `symsOk` passes are at distinct addresses. -/
theorem nodup_of_symsOk {base : Nat} {prog : Program} {syms : List (String × Nat)}
    (h : symsOk base prog syms = true) : (syms.map (·.2)).Nodup := by
  simp only [symsOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- The data symbols `symsOk` passes are none below the code (the premise
of `lays_threadAt`, `endPc_threadAt` and `label_threadAt_of_codeOf`). -/
theorem above_of_symsOk {base : Nat} {prog : Program} {syms : List (String × Nat)}
    (h : symsOk base prog syms = true) : ∀ p ∈ syms, base ≤ p.2 := fun p hp => by
  have := codeEnd_lt_of_symsOk h p hp
  simp only [codeEnd] at this
  omega

/-- **The canonical loader's thread has a valid layout** when its program
has no empty data directive and its data symbols pass `symsOk`. -/
theorem validLayout_threadAt {E : Entry} {base : Nat} {prog : Program} {syms : List (String × Nat)}
    (hcode : prog.all (fun d => Kraken.Executable.cellOk (d, d.fakeSize)) = true)
    (hsyms : symsOk base prog syms = true) :
    Kraken.Executable.ValidLayout (threadAt E base prog syms).exe := by
  simp only [symsOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hsyms
  obtain ⟨⟨hlen, hab⟩, hnd⟩ := hsyms
  let le : String × Nat → String × Nat → Bool := fun a b => decide (a.2 ≤ b.2)
  have hperm := List.mergeSort_perm syms le
  have hsorted : (syms.mergeSort le).Pairwise (fun a b => le a b) :=
    List.pairwise_mergeSort (fun a b c hab hbc => by simp only [le, decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) syms
  have hnd' : ((syms.mergeSort le).map (·.2)).Nodup := hnd.perm (hperm.map _).symm
  have hlt : (syms.mergeSort le).Pairwise (fun a b => a.2 < b.2) := by
    have := List.Pairwise.and hsorted (List.pairwise_map.mp hnd')
    refine this.imp fun {a b} h => ?_
    simp only [le, decide_eq_true_eq] at h
    omega
  have hin : ∀ p ∈ syms.mergeSort le, codeEnd base prog < p.2 ∧ p.2 < base + 2 ^ 64 := fun p hp => by
    have := hab p (hperm.mem_iff.mp hp)
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
  obtain ⟨new, h1, h2, h3, h4⟩ := placeStep_fold (syms.mergeSort le) [] (codeEnd base prog) (base + 2 ^ 64)
    hin hlt (by simp only [codeEnd]; omega)
  have hcells : (threadAt E base prog syms).exe.2 = prog.map (fun d => (d, d.fakeSize)) ++ new := by
    rw [threadAt_exe_eq_old (fun p hp => (hin p (hperm.mem_iff.mpr hp)).1) hnd]
    show prog.map (fun d => (d, d.fakeSize)) ++ PlaceSyms.placeSymsOld _ _ _ _ = _
    rw [PlaceSyms.placeSymsOld]
    exact congrArg _ h1
  refine Kraken.Executable.validLayout_of_cellsOk _ ?_ ?_
  · rw [hcells, List.all_append, Bool.and_eq_true]
    refine ⟨?_, List.all_eq_true.mpr h2⟩
    simpa [List.all_map, Function.comp_def] using hcode
  · rw [hcells, List.map_append, List.sum_append, List.map_map]
    have : (prog.map ((·.2) ∘ fun d => (d, d.fakeSize))) = prog.map Directive.fakeSize := rfl
    rw [this]
    simp only [codeEnd] at h3 h4
    omega

end Loaded

end Scc.Cert.Rt.A64
