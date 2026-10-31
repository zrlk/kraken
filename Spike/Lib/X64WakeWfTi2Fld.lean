/-
**The second TCB's words, the take's counters and the box's placement at
`h1`'s memory side** (x86-64, the twin of `Spike/Lib/A64WakeWfTi2Fld.lean`
and of `A64WakePlacedCal.hti_placed`): the premises `hpl`, `hmF`, `hnoF`,
`hoffT`, `hoffL`, `hoffX`, `hfld` of `X64.WakeTi2Hat.hti_W` at
`Ly := RuntimeLayout.ofPlaceWX hp i` and
`ms1 := WakeH1Inv.ms1W asm hp i E cT ls0 l b n []` (`hunF` passes through as
`hfld2_W`'s premise).

The second TCB `t2 = pinA + 104` has its six words in `[pinA + 104, pinA +
152)`, in `pinned` (`hpin2`); the counters `lockA`, `nextA` are runtime
words (`words_mapped`). Both lie in `.data` or `pinned`, disjoint from the
heap that holds `l`'s box (`AllocLand`), the start's label `L0T` none of them
(no static labels, `hstat`; main's `ThreadId` box sized `0`).

- `hti_placedX`: `hpl`, main's box source placed (`PlacedLy.placedSE_boxAt`
  at main's slots `-16`, `-8`), given `l` fresh (`hl`).
- `hoffL_W`, `hoffX_W`: the lock and the next offset off wake's arena.
- `hoffT2_W`, `hmF2_W`: the TCB's words off the arena and mapped.
- `hnoF2_W`: the TCB's words none of `own2b`'s (A13's data part: apart from
  the runtime's words and from `scc_rt_nthreads`).
- `hfld2_W`: `scc_rt_thread_init`'s six stores (`StOk`); `G` is `GOf2`'s,
  the limit word `pinA + 112` holding `lim2V`.
- `t2_eq`, `pin_add`, `tcb_word`, `tcb_bytes`, `rt_dp`, `stOk_tcb`: the
  TCB's words (`spawnWords`', in `pinned`); a word of `.data` or `pinned` is
  the runtime's at `ms1`.

**Unlike AArch64**: the assembly is a parameter `asm`; `StOk` has no exit
pc; the source fact is `QB`'s (no `SB`), main's slots `-16`, `-8` (A64 `-72`,
`-80`); the off-arena helpers are `X64WakeWfCalOff`'s (`CalWf`), the pinned
bounds `CalWf.pin2_toNat`/`pin2_contains`. No absolute address appears in
this file.
-/
import Spike.Lib.X64WakeWfCalOff
import Spike.Lib.X64WakeH1Inv
import Spike.Lib.X64WakeOwn2
import Spike.Lib.X64WakeOwnSW
import Spike.Lib.X64WakeWcSp3Seg
import Spike.Lib.X64WakePlacedLy
import Spike.Lib.Rt.X64RtTi

namespace Spike.Lib.X64.WakePh.Ti2Fld

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.WakeWc (t2)
open Spike.Lib.X64WakeLoadT (L0T ls0T tcb0)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64WakeGOf2 (lim2A gOf2_ne pin_ne2 gOf2_lim2V)
open Spike.Lib.X64.PhRec (pin_ne)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64.WakeHMid (QB)

/-- **`hti_W`'s `hpl`**: main's source at the box placed, `o` at main's
slot `-16` (the cell `b`), `me` at `-8` (main's id), `l` fresh at the
start (`hl`). -/
theorem hti_placedX {Λ : Scc.Sem.Layout} {l : WeakMem.AllocLabel} {b : Nat} {R : Region} (hl : L0T Λ l = none) :
    ∀ c0, (∃ l' A', QB l b l' A' c0) → ∀ s : State,
      placeVal (machine (kernel 1)) s (.slot (R.addr (-16)).toNat) = some b →
      placeVal (machine (kernel 1)) s (.slot (R.addr (-8)).toNat) = some (tcb0 Λ) →
      Spike.Lib.X64ConsumerS.PlacedSE Λ (Spike.Lib.X64ConsumerA.upd (L0T Λ) l b) s c0 [] := by
  rintro c0 ⟨l', A', rfl, rfl, ht, -, ho, hme⟩ s h16 h8
  exact Spike.Lib.X64.WakePh.PlacedLy.placedSE_boxAt _ _ ht ho hme
    ⟨_, h16, Spike.Lib.X64.WakePh.PlacedLy.lbl_l _ _ _⟩
    ⟨_, h8, Spike.Lib.X64.WakePh.PlacedLy.lbl_me _ (Spike.Lib.X64.WakePh.PlacedLy.ne_of_fresh hl)⟩

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (ls0 : Spike.Lib.X64Consumer.Lsize) (l : WeakMem.AllocLabel) (b n : Nat)
  {F : MachineData → Prop}

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
/-- `h1`'s memory side at no frames. -/
local notation "ms1" => WakeH1Inv.ms1W asm hp i E cT ls0 l b n []

/-- **`hti_W`'s `hoffL`**: `scc_rt_stack_lock` is off wake's arena. -/
theorem hoffL_W :
    ¬ ((WakeOD.arW hp i).heap ≤ (Ly).lockA.toNat ∧
        (Ly).lockA.toNat < (WakeOD.arW hp i).heap + 16 * (WakeOD.arW hp i).cells) ∧
      (⟨(Ly).lockA, 8⟩ : Loc) ≠ (WakeOD.arW hp i).ctrLoc :=
  CalWf.off_of hp i (by simpa using ((Ly).words_mapped _ (Ly).lock_mem).2.2 0 (by decide))
    (CalWf.ne_of_sep (Scc.Cert.Rt.X64.ctrSep_of_rtWordsOk (Spike.Lib.PlaceWX.rtWordsOk_link_of_placeWX i hp) _
      (Ly).lock_mem))

/-- **`hti_W`'s `hoffX`**: `scc_rt_stack_next` is off wake's arena. -/
theorem hoffX_W :
    ¬ ((WakeOD.arW hp i).heap ≤ (Ly).nextA.toNat ∧
        (Ly).nextA.toNat < (WakeOD.arW hp i).heap + 16 * (WakeOD.arW hp i).cells) ∧
      (⟨(Ly).nextA, 8⟩ : Loc) ≠ (WakeOD.arW hp i).ctrLoc :=
  CalWf.off_of hp i (by simpa using ((Ly).words_mapped _ (Ly).next_mem).2.2 0 (by decide))
    (CalWf.ne_of_sep (Scc.Cert.Rt.X64.ctrSep_of_rtWordsOk (Spike.Lib.PlaceWX.rtWordsOk_link_of_placeWX i hp) _
      (Ly).next_mem))

/-- The second TCB is `pinA + 104`. -/
theorem t2_eq : t2 (Ly).lab = (Ly).pinA + 104#64 := by
  show Ret0.pinA (Ly).lab + 104#64 = _; rw [(Ly).lab_pin]

/-- The TCB's word `c` as `pinA + (104 + c)`. -/
theorem pin_add (c : Nat) : (Ly).pinA + 104#64 + BitVec.ofNat 64 c = (Ly).pinA + BitVec.ofNat 64 (104 + c) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

/-- **A word of the second TCB** is `pinA + 80 + 8 (3 + k)`, `spawnWords`'
word `3 + k`. -/
theorem tcb_word {a : BitVec 64} (ha : a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (t2 (Ly).lab)) :
    ∃ k < 6, a = (Ly).pinA + BitVec.ofNat 64 (80 + 8 * (3 + k)) := by
  rw [t2_eq hp i] at ha
  simp only [Spike.Lib.X64.Rt.Ti.tiAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, pin_add hp i _⟩
  · exact ⟨1, by decide, pin_add hp i _⟩
  · exact ⟨2, by decide, pin_add hp i _⟩
  · exact ⟨3, by decide, pin_add hp i _⟩
  · exact ⟨4, by decide, pin_add hp i _⟩
  · exact ⟨5, by decide, pin_add hp i _⟩

/-- A word of `[pinA + 104, pinA + 152)`: its bytes in `pinned`. -/
theorem tcb_bytes (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) {k : Nat} (hk : k < 6) :
    ∀ j < 8, (Ly).Λ.pinned.contains (((Ly).pinA + BitVec.ofNat 64 (80 + 8 * (3 + k))).toNat + j) := by
  have ht := CalWf.pin2_toNat hp i (c := 80 + 8 * (3 + k)) (by omega)
  exact fun j hj => CalWf.pin2_contains hp i hpin2 (by omega) (by omega)

/-- **`hti_W`'s `hoffT`**: the second TCB's words are off wake's arena. -/
theorem hoffT2_W (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hcz : Spike.Lib.X64.Rt.CtrZ o) :
    ∀ a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (t2 (Ly).lab),
      ¬ ((WakeOD.arW hp i).heap ≤ a.toNat ∧ a.toNat < (WakeOD.arW hp i).heap + 16 * (WakeOD.arW hp i).cells) ∧
      (⟨a, 8⟩ : Loc) ≠ (WakeOD.arW hp i).ctrLoc := by
  intro a ha
  obtain ⟨k, hk, rfl⟩ := tcb_word hp i ha
  exact CalWf.hoffPin_W hp i hpin2 hcz (by omega)

/-- **`hti_W`'s `hmF`**: the second TCB's words are mapped for a write. -/
theorem hmF2_W (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) :
    ∀ a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (t2 (Ly).lab),
      Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 (Ly).Λ) true ⟨a, 8⟩ = true := by
  intro a ha
  obtain ⟨k, hk, rfl⟩ := tcb_word hp i ha
  exact Spike.Lib.X64Consumer.mapped_K0_of_mem fun j hj => .inr (tcb_bytes hp i hpin2 hk j hj)

/-- **`hti_W`'s `hnoF`**: the second TCB's words are none of `own2b`'s
(A13's data part: `spawnWords` apart from the runtime's words and from
`scc_rt_nthreads`). -/
theorem hnoF2_W (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (t2 (Ly).lab), ∀ j w,
      (⟨a, 8⟩, w) ∉ Spike.Lib.X64.WakePh.own2b (Ly) (ntA (Ly).lab) j := by
  intro a ha j w hw
  have hw' : a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA, ntA (Ly).lab] := by
    simp only [Spike.Lib.X64.WakePh.own2b, Spike.Lib.X64.WakePh.ownV, List.mem_cons, List.not_mem_nil,
      or_false] at hw
    rcases hw with h | h | h | h | h <;>
      (have e := congrArg (fun x : Loc × Val => x.1.addr) h; simp only [] at e; rw [e]; simp)
  obtain ⟨k, hk, rfl⟩ := tcb_word hp i ha
  have hnt := Spike.Lib.X64.WakePh.ntA_W hp i hA13
  have hm : (Ly).pinA + BitVec.ofNat 64 (80 + 8 * (3 + k)) ∈ Scc.Cert.Spawn.X64.spawnWords (Ly).pinA :=
    List.mem_map.2 ⟨3 + k, List.mem_range.2 (by simp only [Scc.IR.Tcb.size, Scc.IR.maxSpawnArgs]; omega), rfl⟩
  simp only [Scc.Cert.Spawn.X64.a13data, Bool.and_eq_true, decide_eq_true_eq] at hA13
  obtain ⟨⟨⟨⟨⟨-, -⟩, hold⟩, -⟩, hpw⟩, -⟩ := hA13
  have hsep : ∀ y ∈ (Ly).rtWords, Scc.Cert.Rt.X64.WordSep ((Ly).pinA + BitVec.ofNat 64 (80 + 8 * (3 + k))) y := by
    intro y hy
    have := List.all_eq_true.mp hold _ (List.mem_cons_of_mem _ hm)
    exact of_decide_eq_true (List.all_eq_true.mp this y hy)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
  rcases hw' with h | h | h | h | h
  · exact CalWf.ne_of_sep (hsep _ (Ly).pn_mem) h
  · exact CalWf.ne_of_sep (hsep _ (Ly).lock_mem) h
  · exact CalWf.ne_of_sep (hsep _ (Ly).freeN_mem) h
  · exact CalWf.ne_of_sep (hsep _ (Ly).next_mem) h
  · rw [hnt] at h
    exact CalWf.ne_of_sep ((List.pairwise_cons.1 hpw).1 _ hm) h.symm

/-- **A word of `.data` or `pinned` is the runtime's at `ms1`**: `l`'s box
lies in the heap (`AllocLand`), main's `ThreadId` box is empty and there
is no static label (`hstat`). -/
theorem rt_dp (hstat : (Ly).Λ.static = fun _ => none)
    (hland : AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n) {x : Nat}
    (hx : (Ly).Λ.data.contains x ∨ (Ly).Λ.pinned.contains x) : (ms1).rt x := by
  show ¬ ∃ l' b', Spike.Lib.X64ConsumerA.upd (L0T (Ly).Λ) l b l' = some b' ∧
    (lrange (Spike.Lib.X64ConsumerA.updN (ls0T ls0) l n) l' b').contains x
  rintro ⟨l', b', hl, hc⟩
  simp only [lrange, Scc.Sem.Range.contains] at hc
  by_cases h : l' = l
  · subst h
    simp only [Spike.Lib.X64ConsumerA.upd, Spike.Lib.X64ConsumerA.updN, ↓reduceIte, Option.some.injEq] at hl hc
    subst hl
    have hh : (WakeOD.arW hp i).heap = (Ly).Λ.heap.lo := rfl
    have hn : (WakeOD.arW hp i).cells = Scc.Cert.PlaceOK.allocCells := rfl
    have hs : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
      Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX (Spike.Lib.PlaceWX.link i hp)
    obtain ⟨-, -, -, hdh, -, -, -, -, hph, -⟩ := (Spike.Lib.PlaceWX.wf_link_of_placeWX i hp).disjoint
    have hdh' : (Ly).Λ.data.Disjoint (Ly).Λ.heap := hdh
    have hph' : (Ly).Λ.heap.Disjoint (Ly).Λ.pinned := hph
    unfold AllocLand at hland
    rw [hh, hn] at hland
    simp only [Scc.Sem.Range.contains, Scc.Sem.Range.Disjoint] at hx hdh' hph'
    omega
  · simp only [Spike.Lib.X64ConsumerA.upd, Spike.Lib.X64ConsumerA.updN, h, ↓reduceIte] at hl hc
    obtain ⟨rfl, rfl⟩ := Spike.Lib.X64WakeLoadT.l0T_some hstat hl
    simp only [ls0T, Spike.Lib.X64ConsumerA.updN, ↓reduceIte] at hc
    omega

/-- **A store to a word of the second TCB at `ms1`**, given its `G`. -/
theorem stOk_tcb (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hstat : (Ly).Λ.static = fun _ => none)
    (hland : AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n)
    (hunT : ∀ a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (t2 (Ly).lab), ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    {a v : BitVec 64} (ha : a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (t2 (Ly).lab))
    (hG : (ms1).G ⟨a, 8⟩ (v.setWidth 128)) : Ret0.StOk ms1 F a v := by
  have hun := hunT a ha
  obtain ⟨k, hk, rfl⟩ := tcb_word hp i ha
  have hin := tcb_bytes hp i hpin2 hk
  refine ⟨rt_dp asm hp i E cT ls0 l b n hstat hland (.inr (by simpa using hin 0 (by decide))),
    ⟨Spike.Lib.X64Consumer.mapped_K0_of_mem fun j hj => .inr (hin j hj),
      fun _ j hj => .inr (.inr (hin j (by simpa [Scc.Sem.Kernel.locBytes] using hj)))⟩, hG, hun⟩

/-- **`hti_W`'s `hfld`**: `scc_rt_thread_init`'s six stores; `G` is
`GOf2`'s, the limit word `pinA + 112` holding `lim2V`. -/
theorem hfld2_W (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hstat : (Ly).Λ.static = fun _ => none)
    (hland : AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n)
    (hunT : ∀ a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (t2 (Ly).lab), ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    ∀ e ∈ Ret0.ThreadInit.fields (t2 (Ly).lab) (Ret0.stacksA (Ly).lab + 16384#64),
      Ret0.StOk ms1 F (t2 (Ly).lab + BitVec.ofNat 64 e.1) e.2 := by
  intro e he
  rw [t2_eq hp i, (Ly).lab_stacks] at he
  simp only [Ret0.ThreadInit.fields, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine stOk_tcb asm hp i E cT ls0 l b n hpin2 hstat hland hunT
      (by rw [t2_eq hp i]; simp [Spike.Lib.X64.Rt.Ti.tiAddrs]) ?_ <;>
    rw [t2_eq hp i] <;> simp only [] <;> rw [pin_add hp i]
  · exact .inr (gOf2_ne (pin_ne (by decide)) (pin_ne2 (by decide)) _)
  · exact .inr gOf2_lim2V
  all_goals exact .inr (gOf2_ne (pin_ne (by decide)) (pin_ne2 (by decide)) _)

end Place

end Spike.Lib.X64.WakePh.Ti2Fld

/-- info: 'Spike.Lib.X64.WakePh.Ti2Fld.hti_placedX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2Fld.hti_placedX

/-- info: 'Spike.Lib.X64.WakePh.Ti2Fld.hoffL_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2Fld.hoffL_W

/-- info: 'Spike.Lib.X64.WakePh.Ti2Fld.hoffX_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2Fld.hoffX_W

/-- info: 'Spike.Lib.X64.WakePh.Ti2Fld.t2_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2Fld.t2_eq

/-- info: 'Spike.Lib.X64.WakePh.Ti2Fld.pin_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2Fld.pin_add

/-- info: 'Spike.Lib.X64.WakePh.Ti2Fld.tcb_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2Fld.tcb_word

/-- info: 'Spike.Lib.X64.WakePh.Ti2Fld.tcb_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2Fld.tcb_bytes

/-- info: 'Spike.Lib.X64.WakePh.Ti2Fld.hoffT2_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2Fld.hoffT2_W

/-- info: 'Spike.Lib.X64.WakePh.Ti2Fld.hmF2_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2Fld.hmF2_W

/-- info: 'Spike.Lib.X64.WakePh.Ti2Fld.hnoF2_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2Fld.hnoF2_W

/-- info: 'Spike.Lib.X64.WakePh.Ti2Fld.rt_dp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2Fld.rt_dp

/-- info: 'Spike.Lib.X64.WakePh.Ti2Fld.stOk_tcb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2Fld.stOk_tcb

/-- info: 'Spike.Lib.X64.WakePh.Ti2Fld.hfld2_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2Fld.hfld2_W
