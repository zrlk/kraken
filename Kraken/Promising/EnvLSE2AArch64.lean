/-
The one-thread link of the FEAT_LSE2 environment logic to `isaLSE2`, AArch64
(design note `Kraken/Promising/EnvWP.md`, "Pair
effects").

`Kraken.AArch64.EnvLSE2` reads an aligned `LDP`/`STP` of two `X` registers at
a 16-byte location of a list `D` as one 16-byte access (`AllEnvLSE2`), as
`isaLSE2` performs it when its thread declares that location
(`toEv`'s `pairIsOneLoc` branch). This file links the two, with the thread's
declarations `declsOf L`: every location of the shared layout `L` declared at
its width, and `D = L`.

- The declarations are a choice made for the link: `isaLSE2` is unchanged (it
  reads whatever `decls` the thread has), and so are `isa` and the litmus
  runs; the link speaks about the runs whose thread declares exactly `L`.
- The link is direct, not through the merged state of `env_link_halt`: the
  thread's machine state is the judgment's (`RelLSE2`), and the environment
  state is related to the Promising memory by `envRel` alone. `MergeRel` and
  `MemRel` are not used, so they need nothing for 16-byte locations. A byte
  of a location of `L` that is in the thread's `dmem` is private on both
  sides (both read it from `dmem`), so no `hsplit` premise is needed either.
- Mixed-size access to a 16-byte location: neither side claims anything. The
  `lastWrite L` environment permits an access only at exactly a location's
  address and width (and `LSE2Disc` asks it to refuse the 8-byte low half of
  a 16-byte location), and the machine with `declsOf L` resolves such an
  access to a mixed-size fault (`Decls.resolve`), whose runs `AllSeq` does not
  constrain.

`allEnvLSE2_seq` is the core (an `AllEnvLSE2` tree in `lastWrite L`, its
accesses served sequentially by the Promising memory through `declsOf L`);
`seqSim_lse2` the simulation; `env_link_halt_lse2` the link for halting runs.
-/
import Kraken.AArch64.EnvLSE2Sound
import Kraken.Promising.EnvLinkTermAArch64
import Kraken.Promising.SeqLinkAArch64Prog

open Kraken

namespace Kraken.Promising.AArch64

/-! ## The declarations of a layout -/

/-- Every location of `L` declared at its width (strict mode). -/
def declsOf (L : SharedLayout) : Decls := { locs := L.map fun p => ⟨p.1, p.2⟩ }

section Decls

variable {L : SharedLayout}

/-- A location of a well-formed layout is resolved to itself. -/
theorem resolve_declsOf (hL : L.WF) {a : BitVec 64} {n : Nat} (h : (a, n) ∈ L) :
    (declsOf L).resolve a n = .ok (loc a n) := by
  have hs : ((L.map fun p => (⟨p.1, p.2⟩ : Loc)).find? (·.addr == a)).isSome :=
    List.find?_isSome.mpr ⟨⟨a, n⟩, List.mem_map_of_mem h, by simp⟩
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hs
  have hla := List.find?_some hl
  obtain ⟨⟨b, m⟩, hbm, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hl)
  simp only [beq_iff_eq] at hla
  subst hla
  have hpos := hL.pos _ _ h
  have hpos' := hL.pos _ _ hbm
  obtain ⟨-, hnm⟩ := hL.disj _ _ _ _ b h hbm (by simpa using hpos) (by simpa using hpos')
  subst hnm
  simp only [Decls.resolve, declsOf, hl, beq_self_eq_true, ite_true]
  rfl

/-- An access to a location of a well-formed layout is an access to it. -/
theorem access_declsOf (hL : L.WF) {σ : Type} {a : BitVec 64} {n : Nat} (h : (a, n) ∈ L)
    (k : Loc → EvTree σ) : EvTree.access (declsOf L) a n k = k (loc a n) := by
  simp only [EvTree.access, resolve_declsOf hL h]

/-- A pair is one declared location exactly when its double width at its
address is a location of `L`. -/
theorem pairIsOneLoc_declsOf {a : BitVec 64} {w : MemWidth} :
    pairIsOneLoc (declsOf L) a w = true ↔ (a, 2 * w.bytes) ∈ L := by
  simp only [pairIsOneLoc, declsOf, List.any_map, List.any_eq_true, Function.comp_apply,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨b, m⟩, hm, rfl, rfl⟩
    exact hm
  · intro h
    exact ⟨_, h, rfl, rfl⟩

/-- `lastWrite L` meets `LSE2Disc` for `D = L` on a well-formed layout: an
8-byte location at the address of a 16-byte one would overlap it. -/
theorem lastWrite_lse2Disc_of_wf (hL : L.WF) : (SharedEnv.lastWrite L).LSE2Disc L :=
  SharedEnv.lastWrite_lse2Disc fun a h16 h8 => by
    have := (hL.disj a 16 a 8 a h16 h8 (by simp) (by simp)).2
    omega

end Decls

/-! ## The environment state along the memory -/

section EnvRel

variable {L : SharedLayout}

private theorem bits_eq (w : MemWidth) : w.bits = 8 * w.bytes := by cases w <;> rfl

/-- Two locations of a well-formed layout at one address are one location. -/
theorem _root_.Kraken.Promising.SharedLayout.WF.eq_of_addr (hL : L.WF) {a : BitVec 64} {n m : Nat} (hn : (a, n) ∈ L)
    (hm : (a, m) ∈ L) : n = m :=
  (hL.disj a n a m a hn hm (by simpa using hL.pos _ _ hn) (by simpa using hL.pos _ _ hm)).2

/-- A write to a location of `L`, in the environment state and in the memory,
keeps them related. -/
theorem envRel_append (hL : L.WF) {g : BitVec 64 → BitVec 128} {mem : Memory} (henv : envRel L g mem)
    {addr : BitVec 64} {n : Nat} (hm : (addr, n) ∈ L) (v : Val) (tid : Nat) :
    envRel L (SharedEnv.upd g addr v) (mem.append { loc := loc addr n, val := v, tid }).1 := by
  intro b m hb
  rw [Memory.finalVal_append]
  by_cases hba : b = addr
  · subst hba
    have := hL.eq_of_addr hm hb
    subst this
    simp [SharedEnv.upd, sharedLoc_eq]
  · have hne : loc addr n ≠ sharedLoc b m := by
      intro h
      exact hba (congrArg Loc.addr h).symm
    simp only [hne, ite_false, SharedEnv.upd, hba]
    exact henv b m hb

/-- The value a load of a location of `L` reads from the memory, at the
location's width, is the environment state's. -/
theorem envRel_val {g : BitVec 64 → BitVec 128} {mem : Memory} (henv : envRel L g mem)
    {addr : BitVec 64} {w : MemWidth} (hm : (addr, w.bytes) ∈ L) :
    (mem.finalVal (loc addr w.bytes)).setWidth w.bits = (g addr).setWidth w.bits := by
  rw [bits_eq]
  exact (henv addr w.bytes hm).symm

/-- The two halves of a 16-byte (generally `2 * w.bytes`-byte) location's
value agree with the environment state's. -/
theorem envRel_pair_val {g : BitVec 64 → BitVec 128} {mem : Memory} (henv : envRel L g mem)
    {addr : BitVec 64} {w : MemWidth} (hm : (addr, 2 * w.bytes) ∈ L) :
    (mem.finalVal (loc addr (2 * w.bytes))).setWidth w.bits = (g addr).setWidth w.bits ∧
      ((mem.finalVal (loc addr (2 * w.bytes))) >>> w.bits).setWidth w.bits =
        ((g addr) >>> w.bits).setWidth w.bits := by
  have h := henv addr (2 * w.bytes) hm
  rw [sharedLoc_eq] at h
  have hb := bits_eq w
  constructor
  · ext i hi
    have := congrArg (fun x => x.getLsbD i) h
    simp only [BitVec.getLsbD_setWidth] at this
    simp only [BitVec.getElem_setWidth]
    have hi' : i < 8 * (2 * w.bytes) := by omega
    simpa [hi'] using this.symm
  · ext i hi
    have := congrArg (fun x => x.getLsbD (w.bits + i)) h
    simp only [BitVec.getLsbD_setWidth] at this
    simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight]
    have hi' : w.bits + i < 8 * (2 * w.bytes) := by omega
    simpa [hi'] using this.symm

end EnvRel

/-! ## The core: an `AllEnvLSE2` tree in `lastWrite L` against the memory -/

section Core

variable {L : SharedLayout}

local notation "LW" => SharedEnv.lastWrite L

/-- `caspTree` on two locations of `L` resolves each half to itself. -/
theorem caspTree_declsOf (hL : L.WF) {σ : Type} {k : RmwKind} {addr : BitVec 64} {w : MemWidth}
    {cmp1 cmp2 new1 new2 : w.type} {ret : w.type → w.type → EvTree σ}
    (h₁ : (addr, w.bytes) ∈ L) (h₂ : (addr + w.bytesv, w.bytes) ∈ L) :
    caspTree (declsOf L) k addr cmp1 cmp2 new1 new2 ret = caspTree {} k addr cmp1 cmp2 new1 new2 ret := by
  simp only [caspTree, access_declsOf hL h₁, access_declsOf hL h₂, EvTree.access_empty, loc]

/-- **The core.** An `AllEnvLSE2` tree relative to `L` in `lastWrite L`, from
an environment state related to the memory: every sequential run of its
translation with the declarations `declsOf L` ends related to a final
environment state that `post` holds of. -/
theorem allEnvLSE2_seq (hL : L.WF) {tid : Nat} {post : MachineState → (BitVec 64 → BitVec 128) → Prop}
    (e : Effects) :
    ∀ (g : BitVec 64 → BitVec 128) (mem : Memory), e.AllEnvLSE2 L LW g post → envRel L g mem →
      (toEv (declsOf L) e).AllSeq tid mem (fun s m => ∃ g', envRel L g' m ∧ post s g') := by
  induction e with
  | done a => intro g mem h henv; exact ⟨g, henv, h⟩
  | unimplemented msg => intro g mem h; exact h.elim
  | syscall => intro g mem h; exact h.elim
  | unaligned_sp sp => intro g mem h; exact h.elim
  | nonmem_load dmem addr w ret ih =>
    intro g mem h henv
    have hm : (addr, w.bytes) ∈ L := h.1
    simp only [toEv, access_declsOf hL hm, EvTree.AllSeq]
    rw [envRel_val henv hm]
    exact ih _ _ g mem (h.2 _ g ⟨rfl, rfl⟩) henv
  | nonmem_store dmem addr v ret ih =>
    intro g mem h henv
    have hm := h.1
    simp only [toEv, access_declsOf hL hm, EvTree.AllSeq]
    exact ⟨ih _ _ _ (h.2 true _ (.inl ⟨rfl, rfl⟩)) (envRel_append hL henv hm _ tid), fun h => nomatch h⟩
  | sync_load k xcl dmem addr w ret ih =>
    intro g mem h henv
    have hm : (addr, w.bytes) ∈ L := h.1
    simp only [toEv, access_declsOf hL hm, EvTree.AllSeq]
    rw [envRel_val henv hm]
    exact ih _ _ g mem (h.2 _ g ⟨rfl, rfl⟩) henv
  | sync_store k xcl dmem addr v ret ih =>
    intro g mem h henv
    have hm := h.1
    simp only [toEv, access_declsOf hL hm, EvTree.AllSeq]
    exact ⟨ih _ _ _ _ (h.2 true _ (.inl ⟨rfl, rfl⟩)) (envRel_append hL henv hm _ tid),
      fun hx => ih _ _ _ _ (h.2 false g (.inr ⟨hx, rfl, rfl⟩)) henv⟩
  | rmw k noRet dmem addr w op ret ih =>
    intro g mem h henv
    have hm : (addr, w.bytes) ∈ L := h.1
    simp only [toEv, access_declsOf hL hm, EvTree.AllSeq]
    have hv := envRel_val henv hm
    have hop : (op ((mem.finalVal (loc addr w.bytes)).setWidth w.bits)).map (·.setWidth 128) =
        rmwOpBits w.bits op (g addr) := by rw [hv]; rfl
    rw [hop, hv]
    have h' := h.2 (g addr)
    cases hr : rmwOpBits w.bits op (g addr) with
    | none => exact ih _ _ g mem (h' g ⟨rfl, by rw [hr]⟩) henv
    | some v => exact ih _ _ _ _ (h' _ ⟨rfl, by rw [hr]⟩) (envRel_append hL henv hm v tid)
  | fence k ok ih =>
    intro g mem h henv
    exact ih () g mem (h.2 g rfl) henv
  | @undefined α inst ret ih =>
    intro g mem h henv
    cases inst with
    | bool => exact fun i => ih _ g mem (h _) henv
    | bitvec w => trivial
    | statusFlags => trivial
  | require_read_access addr w ok ih => intro g mem h henv; exact ih () g mem h henv
  | require_write_access addr w ok ih => intro g mem h henv; exact ih () g mem h henv
  | require_exec_access p ok ih => intro g mem h henv; exact ih () g mem h henv
  | @rmw_pair k dmem addr w cmp1 cmp2 new1 new2 ret ih =>
    intro g mem h henv
    obtain ⟨hm₁, hm₂, hK⟩ := SharedEnv.lastWrite_caspEnv_iff.mp h
    simp only [toEv]
    rw [caspTree_declsOf hL hm₁ hm₂]
    refine caspTree_allSeq (P := fun o₁ o₂ m => ∃ g', envRel L g' m ∧ (ret o₁ o₂ dmem).AllEnvLSE2 L LW g' post)
      (fun o₁ o₂ m ⟨g', hg', h⟩ => ih o₁ o₂ dmem g' m h hg') ?_
    simp only [envRel_val henv hm₁, envRel_val henv hm₂]
    split
    · rename_i hc
      simp only [SharedEnv.caspLW, hc] at hK
      have hne := MemWidth.add_bytesv_ne addr w
      have hcomm : SharedEnv.upd (SharedEnv.upd g (addr + w.bytesv) (new2.setWidth 128)) addr (new1.setWidth 128) =
          SharedEnv.upd (SharedEnv.upd g addr (new1.setWidth 128)) (addr + w.bytesv) (new2.setWidth 128) := by
        funext x
        simp only [SharedEnv.upd]
        by_cases h1 : x = addr <;> by_cases h2 : x = addr + w.bytesv <;> simp_all
      refine ⟨⟨_, envRel_append hL (envRel_append hL henv hm₁ _ tid) hm₂ _ tid, hK⟩,
        ⟨_, ?_, hK⟩⟩
      rw [← hcomm]
      exact envRel_append hL (envRel_append hL henv hm₂ _ tid) hm₁ _ tid
    · rename_i hc
      simp only [SharedEnv.caspLW, hc] at hK
      exact ⟨g, henv, hK⟩
  | sync_load_pair k xcl dmem addr w ret ih =>
    intro g mem h henv
    obtain ⟨rfl, h₁, h₂⟩ := h
    simp only [toEv]
    by_cases hm : (addr, 2 * w.bytes) ∈ L
    · simp only [pairIsOneLoc_declsOf.mpr hm, ↓reduceIte]
      simp only [access_declsOf hL hm, EvTree.AllSeq]
      obtain ⟨hv₁, hv₂⟩ := envRel_pair_val henv hm
      rw [hv₁, hv₂]
      exact ih _ _ _ g mem ((h₁ hm).2 _ g ⟨rfl, rfl⟩) henv
    · simp only [show ¬pairIsOneLoc (declsOf L) addr w = true from fun h => hm (pairIsOneLoc_declsOf.mp h),
        Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hok₁, h₂⟩ := h₂ hm
      have hm₁ : (addr, w.bytes) ∈ L := hok₁
      obtain ⟨hok₂, h₂⟩ := h₂ _ g ⟨rfl, rfl⟩
      have hm₂ : (addr + w.bytesv, w.bytes) ∈ L := hok₂
      simp only [access_declsOf hL hm₁, access_declsOf hL hm₂, EvTree.AllSeq]
      rw [envRel_val henv hm₁, envRel_val henv hm₂]
      exact ih _ _ _ g mem (h₂ _ g ⟨rfl, rfl⟩) henv
  | @sync_store_pair k xcl dmem addr w v1 v2 ret ih =>
    intro g mem h henv
    obtain ⟨rfl, h₁, h₂⟩ := h
    simp only [toEv]
    by_cases hm : (addr, 2 * w.bytes) ∈ L
    · simp only [pairIsOneLoc_declsOf.mpr hm, ↓reduceIte]
      simp only [access_declsOf hL hm, EvTree.AllSeq]
      exact ⟨ih _ _ _ _ ((h₁ hm).2 true _ (.inl ⟨rfl, rfl⟩)) (envRel_append hL henv hm _ tid),
        fun h => nomatch h⟩
    · simp only [show ¬pairIsOneLoc (declsOf L) addr w = true from fun h => hm (pairIsOneLoc_declsOf.mp h),
        Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hok₁, h₂⟩ := h₂ hm
      have hm₁ := hok₁
      obtain ⟨hok₂, h₂⟩ := h₂ true _ (.inl ⟨rfl, rfl⟩)
      have hm₂ := hok₂
      simp only [access_declsOf hL hm₁, access_declsOf hL hm₂, EvTree.AllSeq, ite_true]
      exact ⟨⟨ih _ _ _ _ (h₂ true _ (.inl ⟨rfl, rfl⟩))
          (envRel_append hL (envRel_append hL henv hm₁ _ tid) hm₂ _ tid), fun h => nomatch h⟩,
        fun h => nomatch h⟩

/-- `toEvCASP`'s one-event `CASP` never applies to an `AllEnvLSE2` tree relative
to `L`: the judgment's `CASP` needs two 8-byte locations of `L`, so its address
is not a 16-byte location of `L`. Every sequential run is as in
`allEnvLSE2_seq`. -/
theorem toEvCASP_allSeq (hL : L.WF) {tid : Nat} {post : MachineState → (BitVec 64 → BitVec 128) → Prop}
    (e : Effects) :
    ∀ (g : BitVec 64 → BitVec 128) (mem : Memory), e.AllEnvLSE2 L LW g post → envRel L g mem →
      (toEvCASP (declsOf L) e).AllSeq tid mem (fun s m => ∃ g', envRel L g' m ∧ post s g') := by
  induction e
  case require_read_access _ _ _ ih => intro g mem h henv; exact ih () g mem h henv
  case require_write_access _ _ _ ih => intro g mem h henv; exact ih () g mem h henv
  case require_exec_access _ _ ih => intro g mem h henv; exact ih () g mem h henv
  case rmw_pair k dmem addr w cmp1 cmp2 new1 new2 ret _ =>
    intro g mem h henv
    cases w
    case W64 =>
      obtain ⟨hm₁, -, -⟩ := SharedEnv.lastWrite_caspEnv_iff.mp h
      have hno : caspIsOneLoc (declsOf L) addr = false := by
        cases hc : caspIsOneLoc (declsOf L) addr with
        | false => rfl
        | true =>
          exfalso
          unfold caspIsOneLoc declsOf at hc
          cases hl : (L.map fun p => (⟨p.1, p.2⟩ : Loc)).find? (·.addr == addr) with
          | none => rw [hl] at hc; cases hc
          | some l =>
          rw [hl] at hc
          have hb : l.bytes = 16 := by simpa using hc
          have hla := List.find?_some hl
          obtain ⟨⟨b, m⟩, hbm, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hl)
          simp only [beq_iff_eq] at hla hb
          subst hla
          have h8 := hL.eq_of_addr hbm hm₁
          simp_all [MemWidth.bytes]
      simp only [toEvCASP, hno, Bool.and_false, Bool.false_eq_true, ite_false]
      exact allEnvLSE2_seq hL _ g mem h henv
    all_goals exact allEnvLSE2_seq hL _ g mem h henv
  all_goals intro g mem h henv; exact allEnvLSE2_seq hL _ g mem h henv

end Core

/-! ## The simulation -/

section Sim

/-- The thread state `x` on the Promising memory is the judgment's state `z`:
the same machine state, the declarations `declsOf L`, and an environment
state related to the memory. -/
def RelLSE2 (L : SharedLayout) (e : _root_.Executable) (endPc : Int64) (x : State × Memory)
    (z : MachineState × (SharedEnv.lastWrite L).State) : Prop :=
  x.1.exe = e ∧ x.1.endPc = endPc ∧ x.1.st = z.1 ∧ x.1.decls = declsOf L ∧ envRel L z.2 x.2

/-- At a cell `(d, sz)` of the text, short of `endPc`, `isaLSE2`'s tree is the
translation of `d`'s FEAT_LSE2 reading (`Directive.interpLSE2`), run with the
continuations `Executable.step` gives it; for a cell other than a `CASP` of `X`
registers (`execLSE2_of_codeAt_casp` for those). -/
theorem execLSE2_of_codeAt [_root_.Layout] {L : SharedLayout} {e : Kraken.Executable Directive}
    [Kraken.Executable.ValidLayout e] {x : State} {d : Directive} {sz : Nat}
    {rest : List (Directive × Nat)} (he : x.exe = e) (hdecls : x.decls = declsOf L)
    (hne : x.st.2 ≠ x.endPc) (hcode : e.codeAt x.st.2 = (d, sz) :: rest) (hx : d.isCaspX = false) :
    isaLSE2.exec x = some ((toEv (declsOf L) (@Directive.interpLSE2 (_root_.Executable.labels e) d
      x.st.1 (.mk x.st.2 (x.st.2 + .ofNat sz)) (fun s' => .done (s', x.st.2 + .ofNat sz))
      (fun pc' s' => .done (s', pc')))).map fun st => { x with st }) := by
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  obtain ⟨exe, endPc', ⟨s, pc⟩, showPc, decls⟩ := x
  simp only at he hdecls hne hcode hat ⊢
  subst he hdecls
  have hdir : ({ exe, endPc := endPc', st := (s, pc), showPc, decls := declsOf L } : State).directive =
      some d := by
    unfold State.directive
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) =
        Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  have hcell : ({ exe, endPc := endPc', st := (s, pc), showPc, decls := declsOf L } : State).cell =
      some (d, sz) := by
    unfold State.cell
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) =
        Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  have hpc' : (pc == endPc') = false := by simpa using hne
  simp only [isaLSE2, execLSE2, hdir, hpc', Option.isNone_some, Bool.or_false, Bool.false_eq_true,
    ite_false]
  letI := Executable.labels exe
  cases hl : lse2Effects { exe, endPc := endPc', st := (s, pc), showPc, decls := declsOf L } with
  | some ef =>
    simp only [lse2Effects, hcell] at hl
    simp only [Directive.interpLSE2, hl, Option.getD_some]
    rfl
  | none =>
    simp only [lse2Effects, hcell] at hl
    rw [Directive.interpLSE2_of_none _ hl]
    simp only [State.isCaspX, hdir, hx, exec, hpc', Option.isNone_some, Bool.or_false, Bool.false_eq_true,
      ite_false]
    congr 2
    unfold Executable.step
    simp only
    rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
    simp only [Directives.interp]

/-- At a `CASP` cell of `X` registers, short of `endPc`, `isaLSE2`'s tree is
the translation of `Directive.interp` by `toEvCASP`. -/
theorem execLSE2_of_codeAt_casp [_root_.Layout] {L : SharedLayout} {e : Kraken.Executable Directive}
    [Kraken.Executable.ValidLayout e] {x : State} {d : Directive} {sz : Nat}
    {rest : List (Directive × Nat)} (he : x.exe = e) (hdecls : x.decls = declsOf L)
    (hne : x.st.2 ≠ x.endPc) (hcode : e.codeAt x.st.2 = (d, sz) :: rest) (hx : d.isCaspX = true) :
    isaLSE2.exec x = some ((toEvCASP (declsOf L) (@Directive.interp (_root_.Executable.labels e) d
      x.st.1 (.mk x.st.2 (x.st.2 + .ofNat sz)) (fun s' => .done (s', x.st.2 + .ofNat sz))
      (fun pc' s' => .done (s', pc')))).map fun st => { x with st }) := by
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  obtain ⟨exe, endPc', ⟨s, pc⟩, showPc, decls⟩ := x
  simp only at he hdecls hne hcode hat ⊢
  subst he hdecls
  have hdir : ({ exe, endPc := endPc', st := (s, pc), showPc, decls := declsOf L } : State).directive =
      some d := by
    unfold State.directive
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) =
        Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  have hcell : ({ exe, endPc := endPc', st := (s, pc), showPc, decls := declsOf L } : State).cell =
      some (d, sz) := by
    unfold State.cell
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) =
        Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  have hpc' : (pc == endPc') = false := by simpa using hne
  letI := Executable.labels exe
  have hl : lse2Effects { exe, endPc := endPc', st := (s, pc), showPc, decls := declsOf L } = none := by
    simp only [lse2Effects, hcell, Directive.interpLSE2?_none_of_isCaspX hx]
  simp only [isaLSE2, execLSE2, hdir, hpc', hl, State.isCaspX, hx, Option.isNone_some, Bool.or_false,
    Bool.false_eq_true, ite_false, ite_true]
  congr 2
  unfold Executable.step
  simp only
  rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
  simp only [Directives.interp]

/-- The FEAT_LSE2 environment judgment simulates the sequential runs of an
`isaLSE2` thread that declares `L`. -/
theorem seqSim_lse2 [_root_.Layout] {L : SharedLayout} (hL : L.WF) (e : Kraken.Executable Directive)
    [Kraken.Executable.ValidLayout e] (endPc : Int64) :
    SeqSim isaLSE2 0 (RelLSE2 L e endPc) (e.instrStepEnvLSE2 L (SharedEnv.lastWrite L)) := by
  rintro ⟨x, mem⟩ ⟨⟨s, pc⟩, g⟩ R ⟨he, hend, hst, hdecls, henv⟩ ⟨d, sz, rest, hcode, hstep⟩ tree hex
  simp only at he hend hst hdecls henv hcode hstep
  have hne : x.st.2 ≠ x.endPc := by
    intro h
    simp [isaLSE2, execLSE2, h] at hex
  rw [hst] at hne
  letI := Executable.labels e
  have hall := Directive.interpLSE2_sound (D := L) (env := SharedEnv.lastWrite L)
    (P := fun st g' => R (st, g')) (next := fun s' g' => R ((s', pc + .ofNat sz), g'))
    (jmp := fun st g' => R (st, g')) (k := fun s' => .done (s', pc + Int64.ofNat sz))
    (fun _ _ h => h) (fun _ _ h => h) hstep
  cases hx : d.isCaspX
  · rw [execLSE2_of_codeAt he hdecls (by rw [hst]; exact hne) (by rw [hst]; exact hcode) hx, hst] at hex
    cases hex
    refine (EvTree.allSeq_map (τ := State) 0 _ _ _ _).mpr ?_
    refine (allEnvLSE2_seq hL (tid := 0) _ g mem hall henv).mono ?_
    rintro st m ⟨g', hg', hR⟩
    exact ⟨(st, g'), ⟨he, hend, rfl, hdecls, hg'⟩, hR⟩
  · rw [execLSE2_of_codeAt_casp he hdecls (by rw [hst]; exact hne) (by rw [hst]; exact hcode) hx, hst] at hex
    cases hex
    refine (EvTree.allSeq_map (τ := State) 0 _ _ _ _).mpr ?_
    rw [Directive.interpLSE2_of_none _ (Directive.interpLSE2?_none_of_isCaspX hx _ _ _)] at hall
    refine (toEvCASP_allSeq hL (tid := 0) _ g mem hall henv).mono ?_
    rintro st m ⟨g', hg', hR⟩
    exact ⟨(st, g'), ⟨he, hend, rfl, hdecls, hg'⟩, hR⟩

end Sim

/-! ## The link -/

/-- **The one-thread FEAT_LSE2 link, halting runs.** As `EnvLinkHaltSafe`
(`EnvLinkSafeAArch64`), for `isaLSE2` with the thread declaring the layout
(`declsOf L`) and the FEAT_LSE2 judgment (`instrStepEnvLSE2 L`), from a
total judgment (`Eventually`). There is no `hsplit` premise: the link is
direct (module doc). -/
def EnvLinkHaltLSE2 : Prop :=
  ∀ [_root_.Layout] (L : SharedLayout) (e : Kraken.Executable Directive) [Kraken.Executable.ValidLayout e],
    L.WF →
    ∀ (A : Arch) (fuel : Nat) (endPc : Int64) (showPc : Int64 → String) (s : MachineData) (pc : Int64)
      (mem : Memory) (g : BitVec 64 → BitVec 128)
      (P : MachineState × (SharedEnv.lastWrite L).State → Prop),
      mem.msgs = #[] → envRel L g mem →
      (∀ x, P x → x.1.2 = endPc) →
      (∀ x R, x.1.2 = endPc → ¬ e.instrStepEnvLSE2 L (SharedEnv.lastWrite L) x R) →
      Eventually (e.instrStepEnvLSE2 L (SharedEnv.lastWrite L)) P ((s, pc), g) →
      ∀ c : Config isaLSE2, ReachablePF A fuel
          ⟨#[Thread.init ({ exe := e, endPc, st := (s, pc), showPc, decls := declsOf L } : State)], mem⟩ c →
        ∀ t' : Thread isaLSE2, c.threads = #[t'] → t'.st.st.2 = endPc →
          ∃ g', envRel L g' c.mem ∧ P ((t'.st.st.1, endPc), g')

theorem env_link_halt_lse2 : EnvLinkHaltLSE2 := by
  intro _ L e _ hL A fuel endPc showPc s pc mem g P hm henv hPend hstuck hev c hc t' ht hend
  obtain ⟨t'', ht'', hcase⟩ := reachablePF_sim A fuel (seqSim_lse2 hL e endPc) hm
    (y := ((s, pc), g)) ⟨rfl, rfl, rfl, rfl, henv⟩ hev hc
  rw [ht] at ht''
  have htt : t' = t'' := by simpa using ht''
  subst htt
  have key : ∀ z, RelLSE2 L e endPc (t'.st, c.mem) z → P z →
      ∃ g', envRel L g' c.mem ∧ P ((t'.st.st.1, endPc), g') := by
    rintro ⟨⟨zs, zpc⟩, zg⟩ ⟨-, -, hst, -, hzg⟩ hP
    have hpc : zpc = endPc := hPend _ hP
    simp only at hst hzg hpc
    subst hpc
    rw [hst]
    exact ⟨zg, hzg, hP⟩
  rcases hcase with ⟨⟨z₁, z₂⟩, x', -, hz, hzx, hPx⟩ | ⟨x', hx, hev'⟩
  · -- `P` was met at `z`, which is at `endPc`, so the thread halted there
    obtain ⟨-, hez, hzst, -, -⟩ := id hzx
    have hpcz : z₁.st.2 = endPc := by rw [hzst]; exact hPend x' hPx
    have hhalt : isaLSE2.exec z₁ = none := by
      simp only at hez
      show execLSE2 z₁ = none
      simp [execLSE2, hpcz, hez]
    cases hz with
    | refl => exact key x' hzx hPx
    | step hex _ _ => rw [hhalt] at hex; cases hex
  · have hpx : x'.1.2 = endPc := by rw [← hx.2.2.1]; exact hend
    cases hev' with
    | done _ hP => exact key x' hx hP
    | step _ _ hT _ => exact absurd hT (hstuck x' _ hpx)

/-! ## For programs -/

/-- At the end address of a laid-out program whose last cell is not a label
there is no FEAT_LSE2 instruction step: the `hstuck` premise of
`env_link_halt_lse2` (the twin of `not_instrStepEnv_of_end`). -/
theorem not_instrStepEnvLSE2_of_end [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {dlast : Directive} (D : SharedEnv.Layout) (env : SharedEnv)
    (hlast : p[p.length - 1]? = some dlast := by rfl)
    (hd : dlast.isLabel = false := by rfl) :
    ∀ x R, x.1.2 = (layout p).addrOf p.length → ¬ (layout p).instrStepEnvLSE2 D env x R := by
  rintro x R hx ⟨d, z, rest, hcode, -⟩
  unfold Kraken.Executable.codeAt at hcode
  rw [hx, Executable.directivesFromAddress_end hlast hd] at hcode
  cases hcode

end Kraken.Promising.AArch64

/-- A FEAT_LSE2 triple on a laid-out program, read at the machine (the twin of
`Program.instrStepEnv_of_tripleEnv`). -/
theorem Program.instrStepEnvLSE2_of_tripleEnvLSE2 [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Executable.ValidLayout (layout p)] {D : SharedEnv.Layout} {env : SharedEnv}
    {P : MachineData → env.State → Prop} {Q : MachineData → env.State → Prop}
    {E : Int64 → MachineData → env.State → Prop} {s : MachineData} {g : env.State}
    (ht : MachineWP.TripleEnvLSE2 D env P p Q E) (hs : P s g)
    (henv : cenv = layout p := by rfl) :
    Eventually ((layout p).instrStepEnvLSE2 D env)
      (fun x => (x.1.2 = (layout p).addrOf p.length ∧ Q x.1.1 x.2) ∨ E x.1.2 x.1.1 x.2)
      ((s, Kraken.Layout.start Directive), g) := by
  have h : (layout p).wpEnvLSE2 D env p Q E s g := henv ▸ ht s g hs
  obtain ⟨hsits, hafter⟩ := Executable.walk_addrOf (p := p) p [] 0 (by simp)
  rw [Nat.zero_add] at hafter
  have hev := h ((layout p).addrOf 0) hsits
  rwa [hafter, Executable.addrOf_zero, Layout.apply_fst] at hev
