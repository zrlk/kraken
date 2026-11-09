/-
**Main taking its own TCB word** (x86-64): the state facts over a
held predicate (`SFactsSt2`) at `ownGX` (`ownG` with main's TCB word
appended, `Spike/Lib/X64WakeOwnS.lean`) at `scc_rt_thread_init`'s first
store `movq %rax, (%rcx)` (`.x7 + 48`, 3 bytes, the node `.st0`), where
`AppOk` fails: `ownS` is `[]` before the store and `[(tcbM, tcbM)]` after
it, the store writing `tcbM` holding `tcbM`. The take is `OwnTree`'s third
case (`OwnUpd`) for the appended map.

- `ownUpd_snoc`, `ownUpd_self`, `ownTree_takeS`: a lone plain store of `V`
  to `A`, `A` none of `ow`'s, stays an `OwnTree` (its third case) with the
  words appended at its leaf `[(A, V)]` (the appended words empty before).
- `SFactsSt2.takeS`: the held-predicate state facts with an appended map
  at such a store, off a system call and the take site.
- `nodeW_st0X`: `.st0`'s states inside `SFactsSt2` at `ownGX L a`, from
  them at `ownG L a`, for `q.tcb = tcbM`, the frame off the stack pool,
  `tcbM` unmapped in private memory under the frame condition, and `tcbM`
  none of `ownG`'s words (`PhRec.TcbSep`, `tcbM ≠ a`).
-/
import Spike.Lib.X64WakeOwnS2
import Spike.Lib.Rt.X64RtTi
import Spike.Lib.X64SpAgree

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.Rt.X64 (codeT codeT_eq blockAtB code_field)
open SccCode (wakeCells)
open Spike.Lib.Consumer1 (OwnTree OwnUpd)
open Spike.Lib.X64 (NodeW ND stDir mB eaddr_mB agrees_of_decls)
open Spike.Lib.X64.Rt (RuntimeLayout tiNAt)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Kraken.Promising.Lower.X64 (exec_store_agrees after)

/-! ## A lone store taking a word -/

/-- An `OwnUpd` of `A` to `V` with `(A, V)` appended. -/
theorem ownUpd_snoc {ow ow' : List (Loc × Val)} {A : Loc} {V : Val} (h : OwnUpd ow ow' A V) :
    OwnUpd ow (ow' ++ [(A, V)]) A V := by
  intro L' w hm
  rcases List.mem_append.mp hm with hm | hm
  · exact h L' w hm
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp hm)
    exact .inl ⟨rfl, rfl⟩

/-- Owning the same words, `A` none of them, is an `OwnUpd` of `A`. -/
theorem ownUpd_self {ow : List (Loc × Val)} {A : Loc} {V : Val} (hd : ∀ w, (A, w) ∉ ow) : OwnUpd ow ow A V :=
  fun L' w hm => .inr ⟨fun he => hd w (by subst he; exact hm), hm⟩

private theorem store_inj {σ : Type} {kr kr' : Kraken.StoreKind} {A A' : Loc} {V V' : Val} {s s'' : σ}
    (h : (EvTree.store kr false A V fun _ => EvTree.done s) = EvTree.store kr' false A' V' fun _ => .done s'') :
    A' = A ∧ V' = V ∧ s'' = s := by
  injection h with h1 h2 h3 h4 h5
  have h6 := congrFun h5 true
  injection h6 with h7
  exact ⟨h3.symm, h4.symm, h7.symm⟩

/-- **A lone store taking `A`**: a plain store of `V` to `A`, none of `ow`'s
words, its leaf's appended words `[(A, V)]`, is the appended map's
`OwnTree` (its third case) from the words `ow` (none appended before). -/
theorem ownTree_takeS {σ : Type} {own ownS : σ → List (Loc × Val)} {ow : List (Loc × Val)}
    {kr : Kraken.StoreKind} {A : Loc} {V : Val} {s' : σ}
    (h : OwnTree own ow (.store kr false A V fun _ => .done s')) (h8 : A.bytes = 8) (hx : ownS s' = [(A, V)])
    (hd : ∀ w, (A, w) ∉ ow) : OwnTree (fun s => own s ++ ownS s) ow (.store kr false A V fun _ => .done s') := by
  refine .inr (.inr (.inl ⟨kr, A, V, s', rfl, h8, ?_⟩))
  show OwnUpd ow (own s' ++ ownS s') A V
  rw [hx]
  apply ownUpd_snoc
  rcases h with ⟨hA, -⟩ | ⟨rfl, kr', L₀, V', s'', he, -, hs⟩ | ⟨kr', L₀, V', s'', he, -, hs⟩ |
    ⟨k, nr, L₀, op, g, he, -⟩
  · have e : own s' = ow := hA.2 true (.inl rfl)
    rw [e]; exact ownUpd_self hd
  · obtain ⟨rfl, rfl, rfl⟩ := store_inj he
    rw [hs]; intro L' w hm; exact .inl (by simpa using hm)
  · obtain ⟨rfl, rfl, rfl⟩ := store_inj he
    exact hs
  · cases he

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Spike.Lib.X64Consumer.Own} {Dt : State → Prop}

/-- **The held-predicate state facts with appended words at a store taking
them**: `s`'s instruction a lone plain store of `V` to `A`, none of `own`'s
words, no words appended at `s` and `[(A, V)]` at its leaf, `s` off a
system call and the take site. -/
theorem _root_.Spike.Lib.X64ConsumerA.SFactsSt2.takeS {ownS : Spike.Lib.X64Consumer.Own} {s s' : State}
    {kr : Kraken.StoreKind} {A : Loc} {V : Val} (h : SFactsSt2 Λ μ own s Dt)
    (hex : isa.exec s = some (.store kr false A V fun _ => .done s')) (h8 : A.bytes = 8) (hs0 : ownS s = [])
    (hs' : ownS s' = [(A, V)]) (hd : ∀ w, (A, w) ∉ own s) (hsys : abi.atSys s = false)
    (htk : ∀ a, μ.site .take = some a → pcOf s ≠ a) :
    SFactsSt2 Λ μ (fun s => own s ++ ownS s) s Dt where
  noSite := h.noSite
  mapped := h.mapped
  svc := h.svc
  ownInstr := fun hns tree he => by
    rw [hex] at he
    cases he
    show OwnTree _ (own s ++ ownS s) _
    rw [hs0, List.append_nil]
    exact ownTree_takeS (h.ownInstr hns _ hex) h8 hs' hd
  ownSys := fun hsy => absurd hsy (by rw [hsys]; decide)
  ownTake := fun a ha hpc => absurd hpc (htk a ha)
  site := h.site
  wrTail := h.wrTail

/-! ## `scc_rt_thread_init`'s first store -/

variable {L : RuntimeLayout} {a : BitVec 64}

/-- A resolved label of the wake cells. -/
private theorem labV (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {y : Nat} (h : codeT lo wakeCells l = some y) : L.lab l = Int64.ofNat y :=
  hlab _ _ (by rw [← codeT_eq]; exact h)

/-- **`tcbM` is none of `ownG`'s words**, off the counters (`TcbSep`) and
`a`. -/
theorem tcbM_notG (hs : PhRec.TcbSep L) (ha : tcbM L ≠ a) (s : State) :
    ∀ w, ((⟨tcbM L, 8⟩ : Loc), w) ∉ ownG L a s := by
  intro w hm
  have h1 := ownG_addr hm
  have h2 := tcbM_sep hs
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h1 h2
  rcases h1 with h | h | h | h | h
  · exact h2 (.inl h)
  · exact h2 (.inr (.inl h))
  · exact h2 (.inr (.inr (.inl h)))
  · exact h2 (.inr (.inr (.inr h)))
  · exact ha h

/-- **`.st0`'s cell at a node state**: the pc `.x7 + 48` (`4199617`), the
store `movq %rax, (%rcx)` (3 bytes) there, its word `q.tcb`. -/
theorem st0_at (hp : L.prog = wakeCells)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {q : Flow.Ret0.TiG} {R : Region}
    {F : MachineData → Prop} {s : State} {c : Spike.Lib.Ctl}
    (hAt : Spike.Lib.X64.At L.exe L.endPc R F (tiNAt L.lab q Flow.Ret0.ThreadInit.x7L .st0) s c) :
    s.st.2 = Int64.ofNat 4199617 ∧ Kraken.Promising.Lower.X64.CellAt s (stDir .rcx 0 .rax) 3 ∧
      Kraken.Promising.Lower.X64.eaddr s 3 (mB .rcx 0) = q.tcb := by
  obtain ⟨hse, hsn, -, hpc, σ, hA, -, hJ⟩ := hAt
  have e7 : L.lab ".Lscc_rt_thread_init.x0" = Int64.ofNat 4199569 := labV hlab (by decide +kernel)
  have hpc' : s.st.2 = Int64.ofNat 4199617 := by
    rw [hpc]; show L.lab ".Lscc_rt_thread_init.x0" + Int64.ofNat 48 = _; rw [e7]; decide
  have hb : blockAtB L.prog ".Lscc_rt_thread_init.x0" 48 [(stDir .rcx 0 .rax, 3)] = true := by
    rw [hp]; decide +kernel
  refine ⟨hpc', (code_field L.lays rfl hb (q := Int64.ofNat 4199617)
    (by show L.lab ".Lscc_rt_thread_init.x0" + Int64.ofNat 48 = _; rw [e7]; decide) s hse hsn).cell0
    rfl rfl hpc', ?_⟩
  have hz : BitVec.ofInt 64 (0 : Int64).toInt = 0#64 := by decide
  refine (eaddr_mB (s : State) 3 .rcx 0).trans ?_
  rw [hA.regs, Reg64s.get64_rcx, hJ.2.2.2, hz, BitVec.add_zero]

/-- **`.st0`'s states inside the held-predicate state facts at `ownGX`**
(main takes `tcbM` there), from them at `ownG`: the store `movq %rax,
(%rcx)` at `.x7 + 48` writes `tcbM` holding `tcbM` (`q.tcb = tcbM`), its
`%rsp` (the frame's `-40`) off the stack pool, `tcbM` unmapped in private
memory (`hun`) and none of `ownG`'s words (`hs`, `ha`). -/
theorem nodeW_st0X (hp : L.prog = wakeCells)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : μ.site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat) (hs : PhRec.TcbSep L)
    (ha : tcbM L ≠ a) {q : Flow.Ret0.TiG} (htcb : q.tcb = tcbM L) {K : State → State → Prop} {R : Region}
    {F : MachineData → Prop}
    (hoff : ¬ (L.Λ.stackPool.lo < (R.addr (-40)).toNat ∧
      (R.addr (-40)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size))
    (hun : ∀ m, F m → Mem.loadInt m.dmem (tcbM L) 8 = none)
    (h : NodeW (fun s _ => SFactsSt2 Λ μ (ownG L a) s Dt) K L.exe L.endPc R F
      (tiNAt L.lab q Flow.Ret0.ThreadInit.x7L .st0)) :
    NodeW (fun s _ => SFactsSt2 Λ μ (ownGX L a) s Dt) K L.exe L.endPc R F
      (tiNAt L.lab q Flow.Ret0.ThreadInit.x7L .st0) := by
  intro s c hAt
  obtain ⟨h1, hK⟩ := h s c hAt
  refine ⟨?_, hK⟩
  obtain ⟨hpc', hc, ha'⟩ := st0_at hp hlab hAt
  rw [htcb] at ha'
  obtain ⟨-, -, hdc, -, σ, hA, hD, hJ⟩ := hAt
  have e7 : L.lab ".Lscc_rt_thread_init.x0" = Int64.ofNat 4199569 := labV hlab (by decide +kernel)
  have eT : L.lab "scc_rt_stack_take" = Int64.ofNat 4199695 := labV hlab (by decide +kernel)
  have eS : L.lab "scc_rt_take_site" = Int64.ofNat 4200277 := labV hlab (by decide +kernel)
  have e1 : L.lab ".Lscc_rt_start.x1" = Int64.ofNat 4198500 := labV hlab (by decide +kernel)
  have eM : L.lab "scc_rt_main" = Int64.ofNat 4198540 := labV hlab (by decide +kernel)
  have hex := exec_store_agrees hc ha' (hun _ hD) (agrees_of_decls hdc _ _)
  have hV : (s.st.1.regs.get (.low .rax .W64)).setWidth 128 = (tcbM L).setWidth 128 := by
    rw [Spike.Lib.X64.Reg64s.get_low64, hA.regs, Reg64s.get64_rax, hJ.2.2.1, htcb]
  rw [hV] at hex
  have hsp := Spike.Lib.X64ConsumerA.rsp_of_abs hA
  dsimp only [tiNAt] at hsp
  have hs0 : ownS L s = [] := by
    unfold ownS
    split
    · rename_i hsel
      exfalso
      unfold selfOwn spPool inPc pcOf at hsel
      rw [hpc', e1, eM, e7, eT, hsp] at hsel
      rcases hsel with h' | h' | h'
      · exact hoff h'.1
      · exact absurd h' (by decide)
      · exact absurd h' (by decide)
    · rfl
  have hs' : ownS L (after s 3 s.st.1) = [(⟨tcbM L, 8⟩, (tcbM L).setWidth 128)] := by
    unfold ownS
    refine ite_eq_left (.inr (.inr ?_))
    show (L.lab ".Lscc_rt_thread_init.x0").toBitVec.toNat + 51 ≤ (s.st.2 + Int64.ofNat 3).toBitVec.toNat ∧
      (s.st.2 + Int64.ofNat 3).toBitVec.toNat < (L.lab "scc_rt_stack_take").toBitVec.toNat
    rw [hpc', e7, eT]; decide
  have hsys : abi.atSys s = false := atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  have htk : ∀ a', μ.site .take = some a' → pcOf s ≠ a' := by
    intro a' ha' hpcs
    rw [hsite] at ha'
    cases ha'
    unfold pcOf at hpcs
    rw [hpc', eS] at hpcs
    exact absurd hpcs (by decide)
  exact h1.takeS hex rfl hs0 hs' (tcbM_notG hs ha s) hsys htk

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.ownTree_takeS' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ownTree_takeS

/-- info: 'Spike.Lib.X64ConsumerA.SFactsSt2.takeS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.SFactsSt2.takeS

/-- info: 'Spike.Lib.X64.WakePh.tcbM_notG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tcbM_notG

/-- info: 'Spike.Lib.X64.WakePh.nodeW_st0X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.nodeW_st0X
