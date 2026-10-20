/-
**The per-access verification conditions of the x64 MS queue for try-once
dequeuers** on `EnvGCAdj`, x64 (`Arch.tso`): the enqueuer is thread `0` on
`planE P`, the dequeuer thread `1` on `planDW P`
(`EnvG/X64MsQueueWGhost.lean`).

**The enqueuer**: `EnvG/X64MsQueue2VC.lean`'s VCs restated at the ghost facts
`GWW` (`ComEW`, `E0W`, `E2W`, `LinkedW`; the phase `PhE` and the plan facts
are reused). The proofs are those of `X64MsQueue2VC`; only the predicate at
the queue words changes (`formW`, whose link and `tail` clauses are `form`'s).

**The dequeuer** reads `head` (`y3`; nothing is recorded), then the link
`[y3]` (`D2W`, the read of value `u`); on `u = 0` it returns empty
(`D2W.back`: its facts unchanged), otherwise it swings `head` from `y3` to
`u` with `lock cmpxchgq` (`vc_w_pop`), releasing `HeadFW` (the overwritten
message adjacent, the link read) and `TokN1` (from `TokQW`: `tokQ` whole, or
an own earlier `head` message of `n1`). On success it records its own
message (`First`, `DoneD2`) and keeps `tokQ` unless it wrote `n1`.
-/
import Kraken.Promising.SLR.EnvG.X64MsQueueWGhost
import Kraken.Promising.SLR.EnvG.X64MsQueue2VC

namespace Kraken.Promising.X64.EnvG.MsQueueX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_of_get? read?_mono prefix_append)
open Kraken.Promising.X64.EnvG.TreiberX (cmpxOp64 cmpxOp64_casMatch)

/-- The try-once dequeuer's environment (thread `1`). -/
noncomputable abbrev EDW (P : Params) : SharedEnv := EnvGCAdj isa Arch.tso 1 (planDW P)

/-- **`NoMsgIn` of an RMW's message from adjacency at the anchor**, at any
location whose release predicate is impure. -/
theorem noMsgIn_of_adjG {tid : Nat} {c : Config isa} {g : Ghost} {tr : Time} {rF : Nat → Res} {T : Nat → Prop}
    (E : Erase rF g T c) {x : Loc} (himp : ∀ v, ¬ Pred.Pure (g.rel x) v)
    (hadj : AdjAt tid c g x tr (c.mem.last + 1)) (w : Msg) : NoMsgIn (c.mem.append w).1 x tr (c.mem.last + 1) := by
  have hwi := hadj.lastAt E himp
  intro p wm h1 h2 hg hl
  have hle : p ≤ c.mem.last := by simp only [Time] at *; omega
  rw [Memory.get?_append_of_le _ _ _ hle] at hg
  have : c.mem.writeIn x tr (c.mem.last + 1 - 1) = true :=
    (Memory.writeIn_iff _ _ _ _).mpr ⟨p, wm, h1, by simp only [Time] at *; omega, hg, hl⟩
  rw [hwi] at this; cases this

theorem sw128_inj {a b : BitVec 64} (h : BitVec.setWidth 128 a = BitVec.setWidth 128 b) : a = b := by
  have := congrArg (BitVec.setWidth 64) h; simpa using this

section Rel

variable {P : Params}

/-- **`formW` of a swing of `tail`**. -/
theorem formW_tail (hL : QLocs P) {m : Memory} {v : Val} {w : Nat} (R : Res)
    (ht : TailF P (m.append ⟨P.tail, v, w⟩).1 (m.last + 1) v) :
    (formW P).P v (m.append ⟨P.tail, v, w⟩).1 (m.last + 1) R := fun _ =>
  ⟨P.tail, w, Memory.get?_append_last _ _, fun hx => absurd hx hL.not_isL_tail,
    fun hx => absurd hx.symm hL.head_tail, fun _ => .inl ht, fun hx => absurd hx.symm hL.head_tail,
    fun hx => absurd hx.symm hL.head_tail⟩

/-- `TailF` of a swing (`X64MsQueue2VC.tailF_of` at `GWW`). -/
theorem tailF_ofW {tid : Nat} {σ : EStateX} {c : Config isa} {g : Ghost} (hanc : AnchorOk tid σ c g)
    {rF : Nat → Res} {T : Nat → Prop} (E : Erase rF g T c) (hW : GWW P g) {tr : Time} {old z y' : Val}
    (htr : tr < c.mem.last + 1) (hrd : c.mem.read? P.tail tr = some old)
    (hadj : AdjAt tid c g P.tail tr (c.mem.last + 1)) (hx : BitVec.setWidth 64 old = BitVec.setWidth 64 z) {b : Time}
    (h2 : σ.snap.mem.read? ⟨BitVec.setWidth 64 z, 8⟩ b = some y') (hnz : BitVec.setWidth 64 y' ≠ 0) (w : Nat) :
    TailF P (c.mem.append ⟨P.tail, BitVec.setWidth 128 (BitVec.setWidth 64 y'), w⟩).1 (c.mem.last + 1)
      (BitVec.setWidth 128 (BitVec.setWidth 64 y')) := by
  obtain ⟨hb, h2'⟩ := read_at_append hanc h2 ⟨P.tail, BitVec.setWidth 128 (BitVec.setWidth 64 y'), w⟩
  exact ⟨by simpa using hnz, tr, old, b, y', htr, read?_mono (prefix_append _ _) hrd,
    noMsgIn_of_adjG E (hW.impure (.inr (.inl rfl))) hadj _, hb, by rw [hx]; exact h2', by simp⟩

end Rel

/-! ## The enqueuer -/

/-- **The enqueuer's common facts** at `GWW`. -/
def ComEW (P : Params) (σ : EStateX) : Prop :=
  GWW P σ.g ∧ (∀ a, 0 < (σ.r.wr ⟨a, 8⟩).q) ∧ TokFrozen P.tokH σ.r

/-- **`enq`**. -/
def E0W (P : Params) (n : BitVec 64) (σ : EStateX) : Prop := ComEW P σ ∧ PhE P n σ
/-- **After `movq (tail),%rbx`** of `y3`. -/
def E1W (P : Params) (n : BitVec 64) (y3 : Val) (σ : EStateX) : Prop :=
  E0W P n σ ∧ ∃ a, σ.snap.mem.read? P.tail a = some y3
/-- **After `movq (%rbx),%rcx`** of `y4`. -/
def E2W (P : Params) (n : BitVec 64) (y3 y4 : Val) (σ : EStateX) : Prop :=
  E1W P n y3 σ ∧ ∃ b, σ.snap.mem.read? ⟨BitVec.setWidth 64 y3, 8⟩ b = some y4
/-- **After the link** of `n` at `[y3]`. -/
def LinkedW (P : Params) (n : BitVec 64) (y3 : Val) (σ : EStateX) : Prop :=
  ComEW P σ ∧ ((n = P.n1 ∧ TokFrozen P.tok2 σ.r) ∨ n = P.n2) ∧
    (∃ L w, σ.snap.mem.get? L = some ⟨⟨BitVec.setWidth 64 y3, 8⟩, BitVec.setWidth 128 n, w⟩) ∧
    ∃ a, σ.snap.mem.read? P.tail a = some y3

section EnqKeep

variable {P : Params} {σ σ' : EStateX} {n : BitVec 64}

theorem ComEW.fence (h : ComEW P σ) (hf : FenceLe σ σ') : ComEW P σ' := by unfold ComEW; rw [hf.g, hf.r]; exact h
theorem E0W.fence (h : E0W P n σ) (hf : FenceLe σ σ') : E0W P n σ' := ⟨h.1.fence hf, h.2.fence hf⟩
theorem E2W.fence {y3 y4 : Val} (h : E2W P n y3 y4 σ) (hf : FenceLe σ σ') : E2W P n y3 y4 σ' :=
  ⟨⟨h.1.1.fence hf, hf.snap ▸ h.1.2⟩, hf.snap ▸ h.2⟩
theorem LinkedW.fence {y3 : Val} (h : LinkedW P n y3 σ) (hf : FenceLe σ σ') : LinkedW P n y3 σ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1.fence hf, by unfold TokFrozen; rw [hf.r]; exact h2, hf.snap ▸ h3, hf.snap ▸ h4⟩
theorem E2W.e0 {y3 y4 : Val} (h : E2W P n y3 y4 σ) : E0W P n σ := h.1.1

theorem ComEW.load {k : LoadKind} {l : Loc} {v : Val} (h : ComEW P σ) (hf : LoadFacts Arch.tso 0 σ σ' k l v) :
    ComEW P σ' := by
  obtain ⟨hanc, hr, -⟩ := hf
  exact ⟨h.1.mono hanc.ghost, hr ▸ h.2⟩

theorem E0W.load {k : LoadKind} {l : Loc} {v : Val} (h : E0W P n σ) (hf : LoadFacts Arch.tso 0 σ σ' k l v) :
    E0W P n σ' := ⟨h.1.load hf, h.2.load hf⟩

theorem ComEW.rmw {k : RmwKind} {addr : BitVec 64} {m : Nat} {op : Val → Option Val} {old : Val} (h : ComEW P σ)
    (hs : (EnvGC isa Arch.tso 0 (planE P)).step (.rmw k addr m op) σ old σ') : ComEW P σ' := by
  refine ⟨h.1.mono (rmw_ghost hs), fun a => ?_, ?_⟩ <;> (try unfold TokFrozen) <;>
    rcases rmw_res hs with hr | ⟨new, tw, Pc, C, -, hr⟩ <;> rw [hr]
  · exact h.2.1 a
  · exact q_op_pos (by rw [afterE_q8]; exact h.2.1 a)
  · exact h.2.2
  · exact q_op_ge_one (by rw [afterE_qH]; exact h.2.2)

end EnqKeep

section Enq

variable {P : Params} {σ : EStateX} {n : BitVec 64}

/-- A load keeps `E0W`. -/
theorem vc_e_loadW (σ : EStateX) (h : E0W P n σ) {k : LoadKind} {xcl : Bool} {a : BitVec 64} {m : Nat} :
    ∀ v (σ' : EStateX), (EE P).step (.load k xcl a m) σ v σ' → E0W P n σ' := fun _ _ hs =>
  h.load (step_loadFacts (pl := planE P) hs)

/-- **VC `movq (tail),%rbx`**. -/
theorem vc_e_load_tailW (σ : EStateX) (h : E0W P n σ) {xcl : Bool} :
    ∀ v (σ' : EStateX), (EE P).step (.load .plain xcl P.tail.addr P.tail.bytes) σ v σ' → E1W P n v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planE P) hs
  obtain ⟨-, -, -, tr, hrd, -⟩ := id hf
  exact ⟨h.load hf, tr, hrd.val⟩

/-- **VC `movq (%rbx),%rcx`**. -/
theorem vc_e_load_linkW (σ : EStateX) {y3 : Val} (h : E1W P n y3 σ) {xcl : Bool} :
    ∀ v (σ' : EStateX), (EE P).step (.load .plain xcl (BitVec.setWidth 64 y3) 8) σ v σ' → E2W P n y3 v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planE P) hs
  obtain ⟨hanc, -, -, tr, hrd, -⟩ := id hf
  exact ⟨⟨h.1.load hf, h.2.imp fun _ ha => hanc.read? ha⟩, tr, hrd.val⟩

/-- **A load keeps `E2W`** (the re-check `cmpq %rbx,(tail)`). -/
theorem vc_e_load2W (σ : EStateX) {y3 y4 : Val} (h : E2W P n y3 y4 σ) {k : LoadKind} {xcl : Bool} {a : BitVec 64}
    {m : Nat} : ∀ v (σ' : EStateX), (EE P).step (.load k xcl a m) σ v σ' → E2W P n y3 y4 σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planE P) hs
  obtain ⟨hanc, -⟩ := id hf
  exact ⟨⟨h.1.1.load hf, h.1.2.imp fun _ ha => hanc.read? ha⟩, h.2.imp fun _ hb => hanc.read? hb⟩

/-- **The enqueuer's swing of `tail`** from `y3` to `y ≠ 0`, the value of a
read of `[y3]`: permitted (`TailF`). -/
theorem ok_e_tailW (hL : QLocs P) (σ : EStateX) (hcom : ComEW P σ) {y3 y' : Val} {y : BitVec 64} {b : Time}
    (h2 : σ.snap.mem.read? ⟨BitVec.setWidth 64 y3, 8⟩ b = some y') (hy : BitVec.setWidth 64 y' = y) (hnz : y ≠ 0) :
    (EE P).ok (.rmw .acqRel P.tail.addr P.tail.bytes (cmpxOp64 (BitVec.setWidth 64 y3) y)) σ := by
  have hW := hcom.1
  have e : ({ addr := P.tail.addr, bytes := P.tail.bytes } : Loc) = P.tail := rfl
  have hq : P.IsW P.tail := .inr (.inl rfl)
  refine ⟨hcom.2.1 _, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_,
    by rw [e, gives_ht hL (.inr rfl)]; simp, fun htr hwb hadj => ?_⟩⟩⟩
  · rw [e, planE_rel] at hr; simp [hq] at hr
  · rw [e]; exact hW.impure hq new
  · obtain ⟨hx, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
    rw [e, hW.rel_w hq]
    obtain ⟨rF, E⟩ := hanc.erase
    have := tailF_ofW hanc E (hW.mono hanc.ghost) htr hrd.val hadj (by rw [hx]) h2 (by rw [hy]; exact hnz) 0
    rw [hy] at this
    exact formW_tail hL _ this

theorem tok_tailW (hL : QLocs P) {σ σ' : EStateX} {op : Val → Option Val} {old : Val}
    (hs : (EnvGC isa Arch.tso 0 (planE P)).step (.rmw .acqRel P.tail.addr P.tail.bytes op) σ old σ') {tok : Loc}
    (hb : tok.bytes = 1) (h : TokFrozen tok σ.r) : TokFrozen tok σ'.r :=
  tok_rmw hb h hs (fun _ _ => by rw [gives_ht hL (.inr rfl)]; simp) rfl

/-- **VC `lock cmpxchgq %rcx,(tail)`** (the helping swing). -/
theorem vc_e_helpW (hL : QLocs P) (σ : EStateX) {y3 y4 : Val} (h : E2W P n y3 y4 σ)
    (hnz : BitVec.setWidth 64 y4 ≠ 0) :
    (EE P).ok (.rmw .acqRel P.tail.addr P.tail.bytes
        (cmpxOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y4))) σ ∧
      ∀ old (σ' : EStateX), (EE P).step (.rmw .acqRel P.tail.addr P.tail.bytes
          (cmpxOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y4))) σ old σ' → E0W P n σ' := by
  obtain ⟨⟨⟨hcom, hph⟩, -⟩, b, h2⟩ := h
  refine ⟨ok_e_tailW hL σ hcom h2 rfl hnz, fun old σ' hs => ?_⟩
  have hs' := envGCAdj_step_iff.mp hs
  refine ⟨hcom.rmw hs', ?_⟩
  rcases hph with ⟨hn, h1, h2⟩ | ⟨hn, h2, hl⟩
  · exact .inl ⟨hn, tok_tailW hL hs' tok1_bytes h1, tok_tailW hL hs' tok2_bytes h2⟩
  · exact .inr ⟨hn, tok_tailW hL hs' tok2_bytes h2, hl.mono (rmw_snap_prefix hs')⟩

/-- **VC `lock cmpxchgq %rsi,(%rbx)`** (the link): it fails (`E0W`) or
succeeds (`LinkedW`). -/
theorem vc_e_linkW (hL : QLocs P) (σ : EStateX) {y3 y4 : Val} (h : E2W P n y3 y4 σ) :
    (EE P).ok (.rmw .acqRel (BitVec.setWidth 64 y3) 8 (cmpxOp64 0 n)) σ ∧
      ∀ old (σ' : EStateX), (EE P).step (.rmw .acqRel (BitVec.setWidth 64 y3) 8 (cmpxOp64 0 n)) σ old σ' →
        (BitVec.setWidth 64 old ≠ 0 ∧ E0W P n σ') ∨ (BitVec.setWidth 64 old = 0 ∧ LinkedW P n y3 σ') := by
  obtain ⟨⟨⟨hcom, hph⟩, a, h1⟩, -⟩ := h
  have hW := hcom.1
  refine ⟨⟨hcom.2.1 _, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun hr => ?_⟩⟩, ?_⟩
  · by_cases hq : P.IsW ⟨BitVec.setWidth 64 y3, 8⟩
    · rw [planE_rel, decide_eq_false_iff_not] at hr; exact absurd hq hr
    · rw [hW.rel_ne hq]; exact Pred.emp_pure _
  · have hq : P.IsW ⟨BitVec.setWidth 64 y3, 8⟩ := by rw [planE_rel] at hr; simpa using hr
    obtain ⟨hz, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
    refine ⟨by decide, hW.impure hq _, tok_not_gives_8 _ _ _, fun htr hwb hadj => ?_⟩
    rw [hW.rel_w hq, planE_give]
    obtain ⟨rF, E⟩ := hanc.erase
    obtain ⟨ha, h1'⟩ := read_at_append hanc h1 ⟨⟨BitVec.setWidth 64 y3, 8⟩, BitVec.setWidth 128 n, 0⟩
    have hTL : TailLoc P _ _ ⟨BitVec.setWidth 64 y3, 8⟩ := ⟨a, y3, ha, h1', rfl⟩
    intro _
    refine ⟨_, 0, Memory.get?_append_last _ _, fun hl => ⟨?_, hTL, tr, old, htr,
      read?_mono (prefix_append _ _) hrd.val, hz, noMsgIn_of_adjG E ((hW.mono hanc.ghost).impure hq) hadj _⟩,
      fun _ => .inr hTL, fun _ => .inr hTL, fun _ => .inl hTL, fun _ => .inl hTL⟩
    rcases hph with ⟨rfl, ht1, -⟩ | ⟨rfl, ht2, hls⟩
    · refine .inl ⟨by simp, ?_⟩
      unfold TokFrozen at ht1 ⊢
      rw [gives_link_n1 hL hl]; simpa [Res.only] using ht1
    · refine .inr ⟨by simp, ?_, ?_⟩
      · unfold TokFrozen at ht2 ⊢
        rw [gives_link_n2 hL hl]; simpa [Res.only] using ht2
      · obtain ⟨V', a', y', v', w', hg', hv', hr'⟩ := hls
        obtain ⟨hV', hg''⟩ := get_at_append hanc hg' ⟨⟨BitVec.setWidth 64 y3, 8⟩, BitVec.setWidth 128 P.n2, 0⟩
        obtain ⟨ha', hr''⟩ := read_at_append hanc hr' ⟨⟨BitVec.setWidth 64 y3, 8⟩, BitVec.setWidth 128 P.n2, 0⟩
        exact ⟨V', _, v', w', hV', hg'', hv', a', y', ha', hr'', rfl⟩
  intro old σ' hs
  have hs' := envGCAdj_step_iff.mp hs
  have hcom' := hcom.rmw hs'
  have hpre := rmw_snap_prefix hs'
  obtain ⟨c, tr, hanc, -, hvle, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
  rcases hbr with ⟨hon, hsnap, hr⟩ | ⟨new, tw, hon, -, -, hws, hwb, -, -, -, -, -⟩
  · refine .inl ⟨(cmpxOp64_casMatch _ _).none _ hon, hcom', ?_⟩
    unfold PhE TokFrozen
    rw [hr]
    exact hph.imp id fun h => ⟨h.1, h.2.1, h.2.2.mono hpre⟩
  · obtain ⟨hz, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
    refine .inr ⟨hz, hcom', ?_, ⟨tw, 0, TreiberCommon.WriteSnap.get?_new hws⟩, a, read?_mono hpre h1⟩
    rcases hph with ⟨rfl, -, ht2⟩ | ⟨rfl, -⟩
    · exact .inl ⟨rfl, tok_rmw tok2_bytes ht2 hs' (fun new hn => by
        obtain ⟨-, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hn; exact tok2_not_gives_n1 hL _) rfl⟩
    · exact .inr rfl

/-- **VC `lock cmpxchgq %rsi,(tail)`** (the own swing). -/
theorem vc_e_swingW (hL : QLocs P) (σ : EStateX) {y3 : Val} (h : LinkedW P n y3 σ) :
    (EE P).ok (.rmw .acqRel P.tail.addr P.tail.bytes (cmpxOp64 (BitVec.setWidth 64 y3) n)) σ ∧
      ∀ old (σ' : EStateX), (EE P).step (.rmw .acqRel P.tail.addr P.tail.bytes
          (cmpxOp64 (BitVec.setWidth 64 y3) n)) σ old σ' → LinkedW P n y3 σ' := by
  obtain ⟨hcom, htok, ⟨L, wL, hgL⟩, a, h1⟩ := h
  have hnz : n ≠ 0 := by rcases htok with ⟨rfl, -⟩ | rfl; exact hL.n1z; exact hL.n2z
  refine ⟨ok_e_tailW hL σ hcom (read?_of_get? hgL) (by simp) hnz, fun old σ' hs => ?_⟩
  have hs' := envGCAdj_step_iff.mp hs
  have hpre := rmw_snap_prefix hs'
  refine ⟨hcom.rmw hs', ?_, ⟨L, wL, Memory.get?_of_prefix hpre.2 hgL⟩, a, read?_mono hpre h1⟩
  exact htok.imp (fun ⟨hn, ht2⟩ => ⟨hn, tok_tailW hL hs' tok2_bytes ht2⟩) id

/-- `LinkedW` of `n1` is `E0W` of `n2`. -/
theorem LinkedW.next (hL : QLocs P) {y3 : Val} (h : LinkedW P P.n1 y3 σ) : E0W P P.n2 σ := by
  obtain ⟨hcom, htok, ⟨L, wL, hgL⟩, a, h1⟩ := h
  rcases htok with ⟨-, ht2⟩ | hn
  · exact ⟨hcom, .inr ⟨rfl, ht2, L, a, y3, _, wL, hgL, by simp, h1⟩⟩
  · exact absurd hn hL.n12

end Enq

/-! ## The dequeuer -/

/-- **The dequeuer's token fact**: `tokQ` whole, or a `head` message of `n1`
in its memory (the release of its own `n1` swing). -/
def TokQW (P : Params) (σ : EStateX) : Prop := TokFrozen P.tokQ σ.r ∨ ∃ V, Deq σ.snap.mem P V P.n1

/-- **The dequeuer's common facts**. -/
def ComDW (P : Params) (σ : EStateX) : Prop :=
  GWW P σ.g ∧ 0 < (σ.r.wr P.head).q ∧ (∀ x, P.IsW x → 1 ≤ σ.r.acq x 0) ∧ TokQW P σ

/-- **A frame fact `Y` of a dequeue** survives the dequeuer's fences, loads
and RMWs. -/
structure YOkW (P : Params) (Y : EStateX → Prop) : Prop where
  fence : ∀ {σ σ' : EStateX}, Y σ → FenceLe σ σ' → Y σ'
  load : ∀ {σ σ' : EStateX} {k : LoadKind} {l : Loc} {v : Val}, Y σ → LoadFacts Arch.tso 1 σ σ' k l v → Y σ'
  rmw : ∀ {σ σ' : EStateX} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val}, Y σ →
    (EnvGC isa Arch.tso 1 (planDW P)).step (.rmw .acqRel addr n op) σ old σ' → Y σ'

/-- **After `movq (%rdx),%rcx`** (the link read of `[y3]`) of `u`. -/
def D2W (P : Params) (Y : EStateX → Prop) (y3 u : Val) (σ : EStateX) : Prop :=
  ComDW P σ ∧ Y σ ∧ ∃ b, σ.snap.mem.read? ⟨BitVec.setWidth 64 y3, 8⟩ b = some u

section DeqKeep

variable {P : Params} {σ σ' : EStateX} {Y : EStateX → Prop}

theorem ComDW.fence (h : ComDW P σ) (hf : FenceLe σ σ') : ComDW P σ' := by
  unfold ComDW TokQW TokFrozen; rw [hf.g, hf.r, hf.snap]; exact h

theorem ComDW.load {k : LoadKind} {l : Loc} {v : Val} (h : ComDW P σ) (hf : LoadFacts Arch.tso 1 σ σ' k l v) :
    ComDW P σ' := by
  obtain ⟨hanc, hr, -⟩ := hf
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1.mono hanc.ghost, hr ▸ h2, hr ▸ h3, ?_⟩
  unfold TokQW TokFrozen; rw [hr]
  exact h4.imp id fun ⟨V, hd⟩ => ⟨V, hd.mono (TreiberCommon.AnchorOk.prefix hanc)⟩

theorem ComDW.rmw {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val} (h : ComDW P σ)
    (hs : (EnvGC isa Arch.tso 1 (planDW P)).step (.rmw .acqRel addr n op) σ old σ') : ComDW P σ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hpre := rmw_snap_prefix hs
  have hnq : ∀ x, P.IsW x → x ≠ P.tokQ := fun x hx he => by
    have := isW_bytes P hx; rw [he] at this; simp [Params.tokQ] at this
  have hwh := planDW_whole P ⟨addr, n⟩
  obtain ⟨c, tr, hanc, -, -, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs
  rcases hbr with ⟨-, -, hr⟩ | ⟨new, tw, hon, -, -, hws, -, -, -, -, ⟨Pc, -, hr⟩, -⟩
  · unfold ComDW TokQW TokFrozen; rw [hr]
    exact ⟨h1.mono (rmw_ghost hs), h2, h3, h4.imp id fun ⟨V, hd⟩ => ⟨V, hd.mono hpre⟩⟩
  rw [ComDW, TokQW, TokFrozen, hr]
  refine ⟨h1.mono (rmw_ghost hs), q_op_pos ?_, fun x hx => ?_, ?_⟩
  · rw [Plan.after_q_of_not_mem _ (hwh new) _ _ _ (not_mem_planDW_gives (hnq _ (.inl rfl)) _ _)]; exact h2
  · show 1 ≤ ((planDW P).after _ new tw Pc σ.r).acq x 0 + _
    rw [Plan.after_acq_of_not_mem _ (hwh new) _ _ _ (not_mem_planDW_gives (hnq x hx) _ _)]
    have := h3 x hx; omega
  rcases h4 with ht | ⟨V, hd⟩
  · by_cases hg : P.tokQ ∈ (planDW P).gives ⟨addr, n⟩ new
    · rw [planDW_gives] at hg
      split at hg
      · next he =>
        obtain ⟨hl, rfl⟩ := he
        exact .inr ⟨tw, _, 1, by rw [TreiberCommon.WriteSnap.get?_new hws, hl], by simp⟩
      · simp at hg
    · exact .inl (q_op_ge_one (by rw [Plan.after_q_of_not_mem _ (hwh new) _ _ _ hg]; exact ht))
  · exact .inr ⟨V, hd.mono hpre⟩

theorem yokW_true : YOkW P fun _ => True := ⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩

theorem yokW_first (x : BitVec 64) : YOkW P (First P x) where
  fence h hf := by unfold First; rw [hf.snap, hf.vwOld]; exact h
  load h hf := by
    obtain ⟨V1, hd, hv⟩ := h
    obtain ⟨hanc, -, -, tr, -, hlv, -⟩ := hf
    exact ⟨V1, hd.mono (TreiberCommon.AnchorOk.prefix hanc), by rw [hlv.vwOld]; exact hv⟩
  rmw h hs := let ⟨V1, hd, hv⟩ := h; ⟨V1, hd.mono (rmw_snap_prefix hs), Nat.le_trans hv (rmw_vle hs).vwOld⟩

theorem D2W.fence (hY : YOkW P Y) {y3 u : Val} (h : D2W P Y y3 u σ) (hf : FenceLe σ σ') : D2W P Y y3 u σ' :=
  ⟨h.1.fence hf, hY.fence h.2.1 hf, hf.snap ▸ h.2.2⟩

/-- **The empty exit** (`u = 0`, `movl $1,%eax`): the dequeuer's facts and
frame, unchanged. -/
theorem D2W.back {y3 u : Val} (h : D2W P Y y3 u σ) : ComDW P σ ∧ Y σ := ⟨h.1, h.2.1⟩

end DeqKeep

section Deq

variable {P : Params} {Y : EStateX → Prop}

/-- **A load keeps `ComDW` and the frame** (the `head` read `movq (%rdi),%rdx`). -/
theorem vc_w_load (hY : YOkW P Y) (σ : EStateX) (h : ComDW P σ ∧ Y σ) {k : LoadKind} {xcl : Bool}
    {a : BitVec 64} {m : Nat} : ∀ v (σ' : EStateX), (EDW P).step (.load k xcl a m) σ v σ' → ComDW P σ' ∧ Y σ' :=
  fun _ _ hs => let hf := step_loadFacts (pl := planDW P) hs; ⟨h.1.load hf, hY.load h.2 hf⟩

/-- **VC `movq (%rdx),%rcx`**: the link read of `[y3]`. -/
theorem vc_w_load_link (hY : YOkW P Y) (σ : EStateX) (h : ComDW P σ ∧ Y σ) {y3 : Val} {xcl : Bool} :
    ∀ v (σ' : EStateX), (EDW P).step (.load .plain xcl (BitVec.setWidth 64 y3) 8) σ v σ' → D2W P Y y3 v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planDW P) hs
  obtain ⟨-, -, -, tl, hrd, -⟩ := id hf
  exact ⟨h.1.load hf, hY.load h.2 hf, tl, hrd.val⟩

/-- **VC `lock cmpxchgq %rcx,(%rdi)`** (the swing: `rax = y3`, `rcx = u ≠ 0`):
permitted (`HeadFW`, `TokN1`); after it `ComDW` and `Y`; on success its own
swing records the dequeue (`First`, and `DoneD2` after a `First`), and
`tokQ` stays unless it wrote `n1`. -/
theorem vc_w_pop (hL : QLocs P) (hpt : P.trk = false) (hY : YOkW P Y) (σ : EStateX) {y3 u : Val}
    (h : D2W P Y y3 u σ) (hnz : BitVec.setWidth 64 u ≠ 0) :
    (EDW P).ok (.rmw .acqRel P.head.addr P.head.bytes
        (cmpxOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 u))) σ ∧
      ∀ old (σ' : EStateX), (EDW P).step (.rmw .acqRel P.head.addr P.head.bytes
          (cmpxOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 u))) σ old σ' →
        ComDW P σ' ∧ Y σ' ∧ (BitVec.setWidth 64 old = BitVec.setWidth 64 y3 →
          First P (BitVec.setWidth 64 u) σ' ∧ ∀ x0, First P x0 σ → DoneD2 σ'.snap.mem P x0 (BitVec.setWidth 64 u)) ∧
        (TokFrozen P.tokQ σ.r → TokFrozen P.tokQ σ'.r ∨
          (BitVec.setWidth 64 old = BitVec.setWidth 64 y3 ∧ BitVec.setWidth 64 u = P.n1)) := by
  obtain ⟨hc, hy, b, hl⟩ := h
  have hW := hc.1
  have e : ({ addr := P.head.addr, bytes := P.head.bytes } : Loc) = P.head := rfl
  have hq : P.IsW P.head := .inl rfl
  refine ⟨⟨hc.2.1, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_, ?_,
    fun htr hwb hadj => ?_⟩⟩⟩, fun old σ' hs => ?_⟩
  · rw [e, planDW_rel] at hr; simp [hq] at hr
  · rw [e]; exact hW.impure hq new
  · rw [e]; exact (planDW_valid P).not_mem_gives _ _
  · obtain ⟨hx, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
    rw [e, hW.rel_w hq, Plan.give_of_whole _ (planDW_whole P _ _)]
    obtain ⟨rF, E⟩ := hanc.erase
    obtain ⟨hbl, hl'⟩ := read_at_append hanc hl ⟨P.head, BitVec.setWidth 128 (BitVec.setWidth 64 u), 1⟩
    have hz : (⟨BitVec.setWidth 64 old, 8⟩ : Loc) = ⟨BitVec.setWidth 64 y3, 8⟩ := by rw [hx]
    refine fun _ => ⟨P.head, 1, Memory.get?_append_last _ _, fun hx' => absurd hx' hL.not_isL_head,
      fun _ => .inl ⟨by simpa using hnz, tr, old, b, u, htr, read?_mono (prefix_append _ _) hrd.val,
        noMsgIn_of_adjG E ((hW.mono hanc.ghost).impure hq) hadj _, hbl, by rw [hz]; exact hl', by simp⟩,
      fun hx' => absurd hx' hL.head_tail, fun _ => .inr (.inl hpt), fun _ => .inr fun _ hn1 => ?_⟩
    simp only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, show 64 ≤ 128 by decide] at hn1
    rcases hc.2.2.2 with ht | ⟨V', vh, w', hg, hv⟩
    · refine .inl ?_
      unfold TokFrozen at ht ⊢
      rw [planDW_gives, ite_eq_left ⟨rfl, by rw [hn1]⟩]; simpa [Res.only] using ht
    · obtain ⟨hV, hg'⟩ := get_at_append hanc hg ⟨P.head, BitVec.setWidth 128 (BitVec.setWidth 64 u), 1⟩
      exact .inr ⟨V', hV, vh, w', hg', hv⟩
  have hs' := envGCAdj_step_iff.mp hs
  refine ⟨hc.rmw hs', hY.rmw hy hs', ?_⟩
  obtain ⟨c, tr, hanc, -, -, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
  rcases hbr with ⟨hon, -, hr⟩ | ⟨new, tw, hon, -, -, hws, hwb, -, hvw, -, ⟨Pc, -, hr⟩, -⟩
  · exact ⟨fun heq => absurd heq ((cmpxOp64_casMatch _ _).none _ hon),
      fun ht => .inl (by unfold TokFrozen; rw [hr]; exact ht)⟩
  obtain ⟨hx, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
  have hdq : Deq σ'.snap.mem P tw (BitVec.setWidth 64 u) :=
    ⟨_, 1, TreiberCommon.WriteSnap.get?_new hws, by simp⟩
  have hV : σ.vs.vwOld < tw := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) (hwb.rel (by decide))
  refine ⟨fun _ => ⟨⟨tw, hdq, hvw (by decide)⟩, fun x0 ⟨V1, hd1, hv1⟩ =>
    ⟨V1, tw, Nat.lt_of_le_of_lt hv1 hV, hd1.mono (rmw_snap_prefix hs'), hdq⟩⟩, fun ht => ?_⟩
  by_cases hn : BitVec.setWidth 64 u = P.n1
  · exact .inr ⟨hx, hn⟩
  · refine .inl ?_
    unfold TokFrozen at ht ⊢; rw [hr]
    refine q_op_ge_one ?_
    rw [Plan.after_q_of_not_mem _ (planDW_whole P _ _)]
    · exact ht
    · rw [e, planDW_gives, ite_eq_right fun h => hn (sw128_inj h.2)]; simp

end Deq

/-! ## The start of each role -/

/-- **`E0W` at the start**: the enqueuer's resource `resEW`. -/
theorem e0_initW (P : Params) (c : Config isa) : E0W P P.n1 (σInitX c (resEW c.mem P) (ghost₀W P)) := by
  have hq : ∀ x, ((σInitX c (resEW c.mem P) (ghost₀W P)).r.wr x).q = fracEW P x := fun _ => rfl
  have hne : ∀ (a : BitVec 64) (b : Nat), b ≠ 8 → ¬((⟨a, b⟩ : Loc) = P.head ∨ (⟨a, b⟩ : Loc) = P.tail) := by
    rintro a b hb (h | h) <;> (simp only [Params.head, Params.tail, Loc.mk.injEq] at h; omega)
  refine ⟨⟨ghost₀W_gww P, fun a => ?_, ?_⟩, .inl ⟨rfl, ?_, ?_⟩⟩
  · rw [hq]; unfold fracEW fracE; simp only [Params.tokQ, Loc.mk.injEq]; split <;> try split
    all_goals grind
  all_goals unfold TokFrozen; rw [hq]
  · simp [fracEW, fracE, Params.tokH, Params.tokQ, hne _ 2 (by decide)]
  · simp [fracEW, fracE, Params.tok1, Params.tokQ, hne _ 1 (by decide)]
  · simp [fracEW, fracE, Params.tok2, Params.tokQ, hne _ 1 (by decide)]

/-- **`ComDW` at the start**: the dequeuer's resource `resDW`. -/
theorem comDW_init (P : Params) (c : Config isa) : ComDW P (σInitX c (resDW c.mem P) (ghost₀W P)) := by
  have hq : ∀ x, ((σInitX c (resDW c.mem P) (ghost₀W P)).r.wr x).q = fracDW P x := fun _ => rfl
  refine ⟨ghost₀W_gww P, ?_, fun x hx => ?_, .inl ?_⟩
  · rw [hq]; simp [fracDW, fracD, Params.tokQ, Params.head]; grind
  · show 1 ≤ (if P.IsW x ∧ (0 : PredId) = 0 then 1 else 0); simp [hx]
  · unfold TokFrozen; rw [hq]; simp [fracDW]

/-! ## A dequeue's frame and the token kept across it -/

/-- **A dequeue's frame**: the first-dequeue records of `g` kept, and the
queue's initial values in the dequeuer's memory. -/
theorem yokW_kept (P : Params) (g : EStateX) :
    YOkW P fun σ => (∀ x0, First P x0 g → First P x0 σ) ∧ InitV σ.snap.mem P where
  fence h hf := ⟨fun x0 hx => (yokW_first x0).fence (h.1 x0 hx) hf, hf.snap ▸ h.2⟩
  load h hf := ⟨fun x0 hx => (yokW_first x0).load (h.1 x0 hx) hf,
    h.2.of_init (TreiberCommon.AnchorOk.prefix hf.1).1⟩
  rmw h hs := ⟨fun x0 hx => (yokW_first x0).rmw (h.1 x0 hx) hs, h.2.of_init (rmw_snap_prefix hs).1⟩


/-- **`tokQ` kept** from `g` to `σ`. -/
def TokKept (P : Params) (g σ : EStateX) : Prop := TokFrozen P.tokQ g.r → TokFrozen P.tokQ σ.r

theorem TokKept.fence {P : Params} {g σ σ' : EStateX} (h : TokKept P g σ) (hf : FenceLe σ σ') :
    TokKept P g σ' := by
  unfold TokKept TokFrozen at *; rw [hf.r]; exact h

theorem TokKept.load {P : Params} {g σ σ' : EStateX} (h : TokKept P g σ) {k : LoadKind} {xcl : Bool}
    {a : BitVec 64} {m : Nat} {v : Val} (hs : (EDW P).step (.load k xcl a m) σ v σ') : TokKept P g σ' := by
  obtain ⟨-, hr, -⟩ := step_loadFacts (pl := planDW P) hs
  unfold TokKept TokFrozen at *; rw [hr]; exact h

/-- `ComDW`, a frame `Y` and `TokKept` through a fence. -/
theorem stW_fence {P : Params} {Y : EStateX → Prop} (hY : YOkW P Y) {g σ σ' : EStateX}
    (h : ComDW P σ ∧ Y σ ∧ TokKept P g σ) (hf : FenceLe σ σ') : ComDW P σ' ∧ Y σ' ∧ TokKept P g σ' :=
  ⟨h.1.fence hf, hY.fence h.2.1 hf, h.2.2.fence hf⟩

/-- A dequeue's result facts through a fence: the own `head` message
(`First`), `DoneD2` after every `First` of `g`, and `tokQ` kept unless the
result is `n1`. -/
theorem resW_fence {P : Params} {g σ σ' : EStateX} {x : BitVec 64}
    (h : First P x σ ∧ (∀ x0, First P x0 g → DoneD2 σ.snap.mem P x0 x) ∧
      (TokFrozen P.tokQ g.r → TokFrozen P.tokQ σ.r ∨ x = P.n1)) (hf : FenceLe σ σ') :
    First P x σ' ∧ (∀ x0, First P x0 g → DoneD2 σ'.snap.mem P x0 x) ∧
      (TokFrozen P.tokQ g.r → TokFrozen P.tokQ σ'.r ∨ x = P.n1) := by
  refine ⟨(yokW_first x).fence h.1 hf, hf.snap ▸ h.2.1, ?_⟩
  unfold TokFrozen at *; rw [hf.r]; exact h.2.2

end Kraken.Promising.X64.EnvG.MsQueueX
