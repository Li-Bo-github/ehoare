require import AllCore SmtMap FSet Array List StdOrder Distr Real Int RealExp PROM.
(*---*) import RealOrder.
require import Xreal RealSeries.
(*---*) import StdBigop.Bigreal.

lemma mkarrayE (l: 'a list) i : (mkarray l).[i] = nth witness l i.
proof. by rewrite getE ofarrayK. qed.

lemma Array_size_eq0 (a:'a array) : size a = 0 <=> a = mkarray [].
proof. 
  split; 1:by move=> ha; apply arrayP; smt(size_mkarray).
  by move=> ->; rewrite size_mkarray.
qed.

lemma nosmt choiceb_uniq ['a] x (P : 'a -> bool) (x0 : 'a) :
     (forall z1 z2, P z1 => P z2 => z1 = z2)
  => P x
  => choiceb P x0 = x.
proof.
move=> hu hx; have /hu /(_ _ hx) // := choicebP P x0 _.
by exists x.
qed.

lemma to_realK_eq (x y: realp) : x%r = y%r <=> x = y.
proof. smt(to_realK). qed.

lemma nosmt rpow_monoE:
  forall (x y z : real),
    1%r < x => x ^ y <= x ^ z <=> y <= z.
proof. by smt(rpowE exp_mono ler_pmul2r ln_gt0). qed.

lemma nosmt rpow_neq0 (x y : real) : 0%r < x => x^y <> 0%r.
proof. by smt(rpowE exp_neq0). qed.


lemma BXA_mulDr (c : real) (P : int -> bool) (F : int -> xreal) l:  BXA.big P (fun x => F x * c%xr) l = (BXA.big P F l)  * c%xr.
proof.
  rewrite -(BXA.big_comp (fun y => y * c%xr)) /=; 1,2: smt(mulmDl). done.
qed.

lemma if_f_cxr (b b1 b2 : 'a -> bool) (f1 f2 : 'a -> xreal):
  (fun a => (if b a then b1 a `|` f1 a else b2 a `|` f2 a)) =
  (fun a => (if b a then b1 a else b2 a) `|` if b a then f1 a else f2 a).
proof. by smt(if_cxr). qed.

op drop_while ['a] (p : 'a -> bool) s =
  with s = []      => []
  with s = x :: s' => if p x then drop_while p s' else s.

lemma drop_while_head_tt ['a] (p : 'a -> bool) (s : 'a list) :
  p (head witness s) => drop_while p s = drop_while p (behead s).
proof. by case s => />. qed.

lemma drop_while_head_ff ['a] (p : 'a -> bool) (s : 'a list) :
  ! (p (head witness s)) => drop_while p s = s.
proof. by case s => />. qed.

lemma size_drop_while  ['a] (p : 'a -> bool) (s : 'a list) :
  size (drop_while p s) <= size s.
proof. elim: s => //= x s ih /#. qed.    

lemma Ep_drestrict ['a] (d : 'a distr) (p : 'a -> bool) (f : 'a -> xreal):
    Ep (drestrict<:'a> d p) f = Ep d (fun x => if p x then f x else 0%xr).
proof. rewrite !/Ep.
  pose g1 := drestrict d p ** f.
  pose g2 := fun (x : 'a) => mu1 d x ** if p x then f x else 0%xr.
  have <- //: g1 = g2.
  rewrite fun_ext /g1 /g2 /( **) => x; rewrite drestrict1E.
  case (p x) => _ //=; by case ((mu1 d x)%rp = 0%rp).
qed.

lemma EpD1 (d : 'a distr) (f : 'a -> xreal) x0 :
    Ep d f = mu1 d x0 ** f x0 + Ep d (fun x => if x <> x0 then f x else 0%xr).
proof.
  rewrite (eq_Ep _ _ ((fun (x : 'a) => if x = x0 then f x0 else 0%xr)
                    + (fun (x : 'a) => if x <> x0 then f x else  0%xr))).
  by move => x * /=; case (x = x0); smt().
  rewrite EpD.
  congr.
  rewrite -Ep_drestrict.
  rewrite (Ep_fin [x0]) 1:/#; 1:smt(drestrict1E).
  rewrite BXA.big_seq1 /= drestrict1E /=.
  trivial.
qed.


abbrev (\o) (d : 'a distr) (h : 'b -> 'a) = mk (mu1 d \o h).

lemma isdistr_inj ['a 'b] (d : 'a distr) (h : 'b -> 'a): injective h => isdistr (mu1 d \o h).
proof.
  move => inj.
  split; 1:smt(ge0_mu1).
  move => S uS.
  pose h' a := choiceb (fun b => h b = a) witness.
  have ->: predT = predT \o h. smt().
  have -> /=: S = map h' (map h S).
  + rewrite -map_comp /(\o); move: uS; elim: S => // [s S ih uS] /=; smt (choicebP).
  rewrite -BRA.big_reindex.
    + move: uS; elim: S => // [s S ih uS x] /=.
      case => xx. smt(choicebP). smt().
  apply le1_mu1_fin. smt(map_inj_in_uniq).
qed.

lemma Ep_reindex ['a 'b] (h : 'a -> 'b) (d : 'b distr) (f : 'b -> xreal) :
  bijective h => Ep d f = Ep (d \o h) (f \o h).
proof.
  move => bij_h.
  rewrite /Ep /=.
  have ->: (fun (x : 'a) => mu1 (d \o h) x ** (\o) f h x) = (d ** f) \o h.
  + apply fun_ext; rewrite /(==).
    move => x. rewrite /( ** ).
    rewrite muK; 1:apply isdistr_inj; smt(bij_inj).
    congr; 1:smt().
    rewrite /psuminf.
    have ->: to_real (d ** f \o h) = to_real (d ** f)  \o h. trivial.
    have ssh: summable (to_real (d ** f)) = summable (to_real (d ** f) \o h).
    + apply eq_iff; apply iffE; split; 1:smt(summable_inj). (* this can surely be done better *)
      case: bij_h => hV [canh canhV].
        have *: to_real (d ** f) = to_real (d ** f) \o h \o hV. by smt(). smt(summable_inj).
    case (summable (to_real (d ** f))) => *; smt(sum_reindex summable_inj bij_inj).
qed.


section Sorted.
  declare type a.
  declare op (<=) : a -> a -> bool.

  lemma sorted_cat_cons (x:a) (l1 l2: a list) : 
    sorted (<=) l1 => sorted (<=) l2 => 
    (forall y, y \in l1 => y <= x) =>
    (forall y, y \in l2 => x <= y) =>
    sorted (<=) (l1 ++ x :: l2).
  proof.
    move=> hs1 hs2 hle hge.
    elim: l1 hs1 hle => [ | y1 l1 hrec /= ^/path_sorted hs1 hp hle] /=.
    + by case: l2 hs2 hge => //= y2 l2 -> /=; apply.
    have {hrec hs1} := hrec hs1 _; 1: by move=> ? h;apply hle; rewrite h.
    smt().
  qed.

  lemma sorted_cat_inv (le: 'a -> 'a -> bool) (l1 l2: 'a list) : 
    sorted le (l1 ++ l2) => 
    sorted le l1 /\ sorted le l2.
  proof.
    elim l1 => [// | y1 l1 hrec /= hp].
    have /hrec {hrec}/> hs _ := path_sorted _ _ _ hp.
    by case: l1 hp hs.
  qed.

  declare axiom le_trans : forall (y x z : a), x <= y => y <= z => x <= z. 
  
  lemma sorted_cat (l1 l2: a list) : 
    sorted (<=) l1 => sorted (<=) l2 => 
    (forall x1 x2, x1 \in l1 => x2 \in l2 => x1 <= x2) =>
    sorted (<=) (l1 ++ l2).
  proof.
    case: l2 => [ | x l2]; 1: by rewrite cats0.
    move=> h1 /= h2 hx; apply sorted_cat_cons => //.
    + by apply: path_sorted h2. 
    + smt().
    by have /allP := order_path_min _ le_trans _ _ h2.
  qed.

end section Sorted.

lemma sorted_map ['a 'b] (e1 : 'a -> 'a -> bool) (e2: 'b-> 'b -> bool) (f : 'a -> 'b) l : 
  (forall x y, e1 x y => e2 (f x) (f y)) =>
  sorted e1 l => sorted e2 (map f l).
proof. move=> hmono; case: l => //= x l; elim: l x => //= /#. qed.

(* ********************************************************************** *)
abstract theory Mem.
  (* Memory addresses                    *)
  type ptr.

  type 'a mem.

  op empty : 'a mem.

  op get : 'a mem -> ptr -> 'a option.
  op "_.[_<-_]" : 'a mem -> ptr -> 'a -> 'a mem.

  op fresh_ptr : 'a mem -> ptr.
  
  axiom mem_eqP ['a] (m1 m2 : 'a mem) : 
    (forall x, get m1 x = get m2 x) <=> m1 = m2.

  axiom emptyE ['a] p : get empty<:'a> p = None. 

  axiom get_setE (m : 'a mem) (p1 p2 : ptr) (v:'a) : 
    get (m.[p1 <- v]) p2 = if p2 = p1 then Some v else get m p2.

  op mem (m : 'a mem) (p : ptr)= get m p <> None.
  abbrev (\in) p (m : 'a mem) = mem m p.

  axiom fresh_ptrP (m : 'a mem) : !fresh_ptr m \in m.

  op "_.[_]" (m : 'a mem) (p : ptr) = oget (get m p).

  lemma mem_setE (m : 'a mem) (p1 p2 : ptr) v : 
     p2 \in (m.[p1 <- v]) = (p2 = p1 \/ p2 \in m).
  proof. smt(get_setE). qed.

  lemma setE (m : 'a mem) (p1 p2 : ptr) (v:'a) : 
    m.[p1 <- v].[p2] = if p2 = p1 then v else m.[p2].
  proof. by rewrite /"_.[_]" get_setE; case: (p2 = p1). qed.

  lemma setE_eq (m : 'a mem) (p : ptr) (v:'a) : 
    m.[p <- v].[p] = v.
  proof. by rewrite setE. qed.

  lemma setE_neq (m : 'a mem) (p1 p2 : ptr) (v:'a) : 
    p2 <> p1 => 
    m.[p1 <- v].[p2] = m.[p2].
  proof. by rewrite setE => ->. qed.

  lemma fresh_ptrE (m : 'a mem) : get m (fresh_ptr m) = None.
  proof. apply (@fresh_ptrP m). qed.

end Mem.

(* A possible implementation of Mem *)
theory MemI.

  clone include Mem with
    type ptr = int, 
    type 'a mem = (ptr, 'a) fmap, 
    op empty ['a] = empty<:ptr, 'a>,
    op fresh_ptr ['a] (m : 'a mem) = 
      listmax Int.(<=) 0 (elems (fdom m)) + 1, 
    op get (m : 'a mem) = "_.[_]" m,
    op "_.[_<-_]" ['a] (m : 'a mem) = "_.[_<-_]" m
    proof *.
  realize mem_eqP by apply fmap_eqP.
  realize emptyE by apply emptyE.
  realize get_setE by apply get_setE.
  realize fresh_ptrP.
  proof.
    move=> m; rewrite /mem /get.
    have h := listmax_gt_in Int.(<=) _ _ 0 (elems (fdom m)).
    + by apply lez_trans. + by apply lez_total.
    case _ : m.[fresh_ptr m] => // x heq.
    have {heq} := h (fresh_ptr m) _.
    + by rewrite -memE mem_fdom /dom heq.
    by rewrite -ltzE. 
  qed.

end MemI.

abstract theory Key.
  type key.

  op (<) : key -> key -> bool.
  op (<=) (x y : key) = x < y \/ x = y.

  axiom lt_trans y x z : x < y => y < z => x < z.
  axiom lt_nle x y : x < y = !y <= x.
  axiom le_total x y : x <= y \/ y <= x.

  lemma le_trans y x z : x <= y => y <= z => x <= z.
  proof. smt(lt_trans). qed.

end Key.

abstract theory EKey.
  clone export Key as K.

  type ekey = [ Minf | K of K.key | Pinf ].

  op (<) (x y : ekey) : bool = 
    with x = Minf, y = Minf => false
    with x = Minf, y = K _  => true
    with x = Minf, y = Pinf => true 
    with x = K kx, y = Minf => false
    with x = K kx, y = K ky => K.(<) kx ky
    with x = K kx, y = Pinf => true 
    with x = Pinf, y = Minf => false
    with x = Pinf, y = K _  => false
    with x = Pinf, y = Pinf => false. 

  clone include Key with 
    type key <- ekey,
    op (<) <- (<)
  proof *.
  realize lt_trans by smt(K.lt_trans).
  realize lt_nle by smt(K.lt_nle).
  realize le_total by smt(K.le_total).

end EKey.

(* ----------------------------------- *)
op hbino : int distr.
axiom hbino1E x : mu1 hbino x = if x < 0 then 0.0 else inv (2.0^(x+1)%r).
axiom hbino_ll : is_lossless hbino.
hint exact random : hbino_ll.

lemma hbino_supp x : x \in hbino <=> 0 <= x.
proof.
  rewrite /support hbino1E.
  split; 1: case: (x < 0) => // /#.
  smt(rpow_int expr_gt0 invr_gt0).
qed.

(* Given Key and a Mem we can implement SkipList *)
abstract theory SkipList.

  clone export Key as K.
  clone export Mem as M.
  type data.

  clone export EKey as EK 
    with theory K <- K.

  type node = { key: ekey; data : data; forward : ptr array }.

  type skip_list = node mem.

  (* Initial skip_list *)
  op m0 = M.empty <:node>.

  op pinf = fresh_ptr m0. 

  op m1 = m0.[pinf <- {| key = Pinf; data = witness; forward = Array.mkarray []; |}].

  op minf = fresh_ptr m1.

  op empty = m1.[minf <- {| key = Minf; data = witness; forward = Array.mkarray [pinf] |}].

  abbrev Key (sl : skip_list) p = sl.[p].`key.

  abbrev Data (sl : skip_list) p = sl.[p].`data.

  abbrev Forward (sl : skip_list) p = sl.[p].`forward.

  abbrev next (sl : skip_list) p = (Forward sl p).[0].

  abbrev height (sl: skip_list) (p:ptr) = size (Forward sl p).

  op with_forward (n:node) (forward : ptr array) = {| n with forward = forward |}.

  op with_data (n:node) (d: data) = {| n with data = d |}.

  op set_next (sl : skip_list) pos h next = 
    let node = sl.[pos] in
    let forward = node.`forward in
    sl.[pos <- with_forward node (forward.[h <- next])].

  op set_minf (sl : skip_list) forward = 
    sl.[minf <- {| key = Minf; data = witness; forward = forward |}].

  (* Concrete implementation *)
  module SL = { 
    (* [find sl k] return the data associated to k in sl, and the cost *)
    proc find (sl:skip_list, k:key) : data option * int = { 
      var nexts, h, cst, next, pos;
     
      cst <- 0;
     
      pos <- minf;
      nexts <- Forward sl pos;
      h <- size nexts - 1;
     
      while(0 <= h) {
        next <- nexts.[h];
        if (K k < Key sl next) {
          h <- h-1;
        } else {
          pos <- next;
          nexts <- Forward sl pos;
        }
        cst <- cst + 1;
      }
      return (if K k = Key sl pos then Some (Data sl pos) else None, cst);
    }

   (* [insert_h sl k d h] insert k in sl with associated data d and height h, if k is in the list do nothing *)
    proc insert_h (sl:skip_list, k:key, d:data, hk: int) : skip_list = {
      var nexts, h, next, pos, pk, fwk, stk;
      
      pos <- minf;
      nexts <- Forward sl pos;
      h <- size nexts - 1;
      stk <- Array.map (fun _ => minf) nexts;
      
      while(0 <= h) {
        next <- nexts.[h];
        if (K k < Key sl next) {
          stk.[h] <- pos;
          h <- h-1;
        } else {
          pos <- next;
          nexts <- Forward sl pos;
        }
      }
      if (K k = Key sl pos) {
        (* the key is already in the skip list, so we just update the data *)
        sl.[pos] <- with_data sl.[pos] d;
      } else {  
        (* The key is not in the skip list, insert it after pos *)

        (* Allocate memory *)
        fwk <- Array.offun (fun _ => pinf) (hk + 1);
        pk <- fresh_ptr sl;

        (* insert the node *)
        h <- 0;
        while (h < size stk /\ h < size fwk) {
          pos <- stk.[h];
          fwk.[h] <- (Forward sl pos).[h];
          sl <- set_next sl pos h pk; (* MA: with_forward?? similar to with_data? *)
          h <- h + 1;
        }
        sl.[pk] <- {| key = K k; data = d; forward = fwk |};
        nexts <- Forward sl minf;
        if (size nexts  < size fwk) {
          nexts <- Array.offun (fun h => if h < size nexts then nexts.[h] else pk) (size fwk);
          sl <- set_minf sl nexts; 
        }
      }
      return sl;
    }

    (* [insert sl e] insert e in sl if e is in the list do nothing *)
    proc insert (sl:skip_list, k:key, d:data) : skip_list = {
      var hk;
      hk <$ hbino;
      sl <@ insert_h(sl, k, d, hk);
      return sl;
    }

    proc build (l : (key * data) list) : skip_list = { 
      var sl, k, d;
      sl <- empty;
      while (l <> []) { 
        (k, d) <- head witness l;
        l <- behead l;
        sl <@ insert (sl, k, d);
      }
      return sl;
    }

    proc build_find (l : (key * data) list, k : key) : int = { 
      var sl, o, c;
      sl <@ build(l);
      (o, c) <@ find(sl, k);
      return c;
    } 

  }.

  (* We start by defining a notion of well formed for a skip-list *)
  (* Order between to node in the skip list *)

  op lt (sl : skip_list) (p1 p2 : ptr) = 
    p1 \in sl /\ p2 \in sl /\ Key sl p1  < Key sl p2.

  op le (sl : skip_list) (p1 p2 : ptr) = 
    (p1 \in sl /\ p1 = p2) \/ lt sl p1 p2.

  op is_path (sl:skip_list) p1 (l:ptr list) p2 =
    with l = "[]" => p1 \in sl /\ p2 = p1
    with l = p::l' => lt sl p1 (next sl p1) /\ 0 < height sl p1 /\ p = next sl p1 /\ is_path sl p l' p2.

  op has_path (sl:skip_list) p1 p2 = exists l, is_path sl p1 l p2.

  op wf_ptr (sl:skip_list) (p:ptr) =
    (p <> pinf => 1 <= height sl p <= height sl minf) /\
    forall h, 0 <= h < height sl p =>
      ((Forward sl p).[h]  <> pinf => h < height sl (Forward sl p).[h]) /\
      exists l,
        is_path sl p (rcons l (Forward sl p).[h]) (Forward sl p).[h]
        /\ all (fun p' => height sl p' <= h) l.

  op wf (sl:skip_list) = 
    sl.[pinf] = {| key = Pinf; data = witness; forward = Array.mkarray []; |} /\ 
    Key sl minf = Minf /\ Data sl minf = witness /\
    (* All pointers are well formed *)
    exists l, 
      is_path sl minf l pinf /\
      forall p, p \in minf :: l => wf_ptr sl p.

  op path sl =
    choiceb (fun l => is_path sl minf l pinf) [].

  (* We now define an abstraction of the skip *)
  
  type dsl = (ekey, data) fmap.
  type hsl = (ekey, int) fmap.

  op bindings (f:node -> 'a) (sl:skip_list) = 
    ofassoc (map (fun p => let n = sl.[p] in (n.`key, f n)) (minf :: path sl)).

  op dsl (sl:skip_list) = bindings (fun n => n.`data) sl.

  op hsl (sl:skip_list) = bindings (fun n => size n.`forward) sl.
 
  abbrev "_.[_]" (sl:hsl) k = oget (sl.[k]).

  op walk_back_step (sl:hsl) (ch:int*int) (k:ekey) =
    let (c, h) = ch in
    let hk = sl.[k] in
    if hk <= h then (c, h) else (c + hk - h - b2i (k = Minf), hk - 1).

  op walk_back (sl:hsl) ch (l: ekey list) = 
    foldl (walk_back_step sl) ch l.

  op elems (sl:hsl) = rev (sort EK.(<=) (elems (fdom sl))).

  op predecessors sl (k:ekey) = 
    let l = (elems sl) in
    let i = find (fun k' => k' <= k) l in
    drop i l.

  op path_len (sl:hsl) k =
    (walk_back sl (0, -1) (predecessors sl k)).`1.

  (* ************************************************************************* *)
  (* lt                                                                        *)
  lemma lt_trans sl y x z : lt sl x y => lt sl y z => lt sl x z.
  proof. smt(EK.lt_trans). qed.

  lemma lt_neq sl x y : lt sl x y => !(le sl y x).
  proof. smt(EK.lt_nle). qed.

  (* ************************************************************************* *)
  (* with_data                                                                 *)

  lemma with_data_key n d : (with_data n d).`key = n.`key by done.
  lemma with_data_data n d : (with_data n d).`data = d by rewrite /with_data.
  lemma with_data_forward n d : (with_data n d).`forward = n.`forward by done.
  hint simplify with_data_key, with_data_data, with_data_forward.

  lemma set_with_data (sl:skip_list) p1 p2 d :
    sl.[p1 <- with_data sl.[p1] d].[p2] = {| key = Key sl p2; data = if p1 = p2 then d else Data sl p2; forward = Forward sl p2; |}.
  proof. rewrite setE; case (p2=p1); smt(). qed.


  lemma set_with_data_forward (sl:skip_list) p1 p2 d :
    Forward sl.[p1 <- with_data sl.[p1] d] p2 = Forward sl p2.
  proof. smt(set_with_data). qed.

  lemma set_with_data_height (sl:skip_list) p1 p2 d :
    height sl.[p1 <- with_data sl.[p1] d] p2 = height sl p2.
  proof. smt(set_with_data). qed.

  lemma set_with_data_key (sl:skip_list) p1 p2 d :
    Key sl.[p1 <- with_data sl.[p1] d] p2 = Key sl p2.
  proof. smt(set_with_data). qed.

 (* ************************************************************************* *)
  (* minf pinf empty                                                           *)

  lemma pinf_minf : pinf <> minf.
  proof.
    apply/negP => heq; have := fresh_ptrP m1 .
    by rewrite -/minf -heq /m1 /= M.mem_setE.
  qed.

  lemma empty_pinf : empty.[pinf] = {| key = Pinf; data = witness; forward = Array.mkarray []; |}.
  proof. by rewrite /empty /m1 !M.setE pinf_minf. qed.

  lemma empty_minf : empty.[minf] = {| key = Minf; data = witness; forward = Array.mkarray [pinf]; |}.
  proof. by rewrite /empty !M.setE. qed.

  lemma pinf_in_empty : pinf \in empty. 
  proof. by rewrite /empty /m1 !M.mem_setE pinf_minf. qed.

  lemma minf_in_empty : minf \in empty.
  proof. by rewrite /empty !M.mem_setE. qed.
  
  lemma is_path_empty : is_path empty minf [pinf] pinf.
  proof.
    rewrite /= /lt /= minf_in_empty empty_minf /= mkarrayE /= pinf_in_empty
      empty_pinf /= size_mkarray /= //.
  qed.

  lemma wf_empty : wf empty.
  proof. 
    rewrite /wf empty_minf empty_pinf /=.
    exists [pinf]; rewrite is_path_empty /= => _ [] ->>; rewrite /wf_ptr.
    + rewrite /height empty_minf /= size_mkarray /=.
      move=> h hh; have ->> : h = 0 by smt().
      by rewrite mkarrayE /=; exists []; rewrite is_path_empty.  
    by rewrite /height empty_pinf /= size_mkarray /= /#.
  qed.

  (* ************************************************************************* *)
  (* Path                                                                      *)

  lemma wf_has_path (sl: skip_list) : wf sl => has_path sl minf pinf. 
  proof. by smt(). qed.
     
  lemma wf_pinf sl : wf sl => Key sl pinf = Pinf.
  proof. by case => ->. qed.

  lemma is_path_trans p2 l1 l2 sl p1 p3 : 
    is_path sl p1 l1 p2 => is_path sl p2 l2 p3 => is_path sl p1 (l1 ++ l2) p3.
  proof. elim: l1 p1 => |> l hrec p1 _ _; apply hrec. qed.
 
  lemma is_path_last sl p1 l p2 :
    is_path sl p1 l p2 => p2 = last p1 l.
  proof. by elim: l p1 => // p l hrec p1 |> _ _ /hrec. qed.

  lemma is_path_cat sl p1 p2 l1 l2: 
    is_path sl p1 (l1 ++ l2) p2 <=> 
     (is_path sl p1 l1 (last p1 l1) /\ is_path sl (last p1 l1) l2 p2).
  proof. by elim: l1 p1 => // /#. qed.

  lemma pathP sl : has_path sl minf pinf => is_path sl minf (path sl) pinf.
  proof. by move=> ?; apply (choicebP (fun (l : ptr list) => is_path sl minf l pinf)). qed.

  lemma is_path_sorted p2 sl p1 l: 
    is_path sl p1 l p2 =>
    sorted (lt sl) (p1::l).
  proof. by elim: l p1 => /= [ // | p l hrec] p1 |> _ _ /hrec. qed.

  lemma is_path_uniq sl p1 p2 l : 
    is_path sl p1 l p2 =>
    uniq (p1::l).
  proof.
    move=> hp; have {hp} := is_path_sorted _ _ _ _ hp.
    elim (p1 :: l) => {p1 p2 l} //= p l hrec ^ hp /path_sorted /hrec -> /=.
    have /allP := order_path_min (lt sl) (lt_trans sl) _ _ hp; smt(lt_nle).   
  qed.

  lemma is_path_lt sl p1 l p2 : is_path sl p1 l p2 => 
    if l = [] then p1 = p2 else lt sl p1 p2.
  proof.
    move => ^ /is_path_last hp /is_path_sorted hs.
    have /allP {hs} := order_path_min (lt sl) (lt_trans sl) p1 l hs.
    case: l hp => // p' l'.
    rewrite (: p'::l' <> []) // lastI last_rcons => ->> h /=; apply h.
    by rewrite mem_rcons. 
  qed.

  lemma is_path_eq_nil sl p l : is_path sl p l p => l = [].
  proof. move=> /is_path_lt; case: l => // ?? /=; smt(lt_nle). qed.

  lemma is_path_inj sl p1 l1 l2 p2 : 
    is_path sl p1 l1 p2 => is_path sl p1 l2 p2 => l1 = l2.
  proof.
    elim: l1 l2 p1 => [ | p l1 hrec] [ | p' l2] p1 => //= |>.
    + move=> hin; apply /negP => -[#hlt hei ->> hp].
      by have /is_path_eq_nil : is_path sl p1 (next sl p1 :: l2) p1 by rewrite /= hlt hei hp.
    + move=> hlt hei hp; apply /negP => -[hin ->>].
      by have /is_path_eq_nil : is_path sl p1 (next sl p1 :: l1) p1 by rewrite /= hlt hei hp.
    by move=> _ _; apply hrec. 
  qed.

  lemma is_path_path sl l : 
    is_path sl minf l pinf => path sl = l.
  proof. 
    move=> hp; have hwf : has_path sl minf pinf by exists l.
    by rewrite (is_path_inj _ _ _ _ _ hp (pathP sl hwf)). 
  qed.

  lemma path_uniq sl : wf sl => uniq (minf::path sl).
  proof. 
    move=> hwf.
    case: (hwf) => /> _ _ l hlp hlwf.
    by have /is_path_uniq := pathP sl (wf_has_path sl hwf).
  qed.
    
  lemma is_path_in sl p1 p2 l p: 
    is_path sl p1 l p2 => 
    p \in (p1 :: l)  =>
    exists l1 l2, is_path sl p1 l1 p /\ is_path sl p l2 p2 /\ l = l1 ++ l2.
  proof.
    elim: l p1 => [ | p' l hrec] |>; 1: by move=> ?; exists [] [].
    move=> p1 hlt hei hp [->> | hin]; 1: by exists [] (next sl p1:: l) => |>; case: hlt.
    by have [l1 l2 [??]]:= hrec _ hp hin; exists (next sl p1 :: l1) l2.
  qed.

  lemma in_path_is_path sl p : 
    has_path sl minf pinf =>  p \in minf::path sl => exists l, is_path sl minf l p.
  proof.
    move=> hwf; have := pathP _ hwf.
    elim: (path sl) minf => |>; 1: by move=> ?; exists [].
    move=> lp hrec p1 hlt hei hpl [-> | hin]; 1: by exists [] => /#.
    by case: (hrec _ hpl hin) => l1 hpl1; exists (next sl p1 :: l1) => |>.
  qed.

  lemma is_path_in_path sl l p :
    has_path sl minf pinf => Key sl pinf = Pinf => is_path sl minf l p => p \in minf::path sl.
  proof.
    move=> hwf hpinf; have := pathP _ hwf.
    elim: (path sl) minf l => /=; 1: smt().
    move=> p1 l1 hrec p0 [ | p2 l2] |> hlt hei hl1 hl2.
    have [] -> //:= hrec _ _ hl1 hl2.
  qed.

  lemma pinf_in_path sl : wf sl => pinf \in minf :: path sl.
  proof.
    move=> hwf; apply (is_path_in_path sl (path sl)).
    + by apply wf_has_path. + by apply wf_pinf.
    by apply/pathP/wf_has_path.
  qed.
 
  lemma is_path_wf_ptr sl l pos : 
    wf sl => is_path sl minf l pos => forall p, p \in minf :: l => wf_ptr sl p.
  proof.
    move=> hwf hpath.
    have hpos := is_path_in_path _ _ _ (wf_has_path sl hwf) _ hpath; 1: by apply: wf_pinf.
    have hp := pathP _ (wf_has_path _ hwf). 
    have |> l1 l2 hl1 hl2 heq := is_path_in _ _ _ _ _ hp hpos.    
    have <<- := is_path_inj _ _ _ _ _ hpath hl1.
    case: (hwf) => |> _ _ _ _ /is_path_path <-; smt(mem_cat).
  qed.

  lemma wf_ptr_last sl l pos : 
    wf sl => is_path sl minf l pos => wf_ptr sl pos.
  proof.
    move=> hwf hpath.
    apply (is_path_wf_ptr _ _ _ hwf hpath).
    by rewrite lastI -(is_path_last _ _ _ _ hpath) mem_rcons. 
  qed.

  lemma is_path_mem (sl:skip_list) p p1 l p2 : 
    is_path sl p1 l p2 => p \in p1::l =>
    p \in sl.
  proof. elim: l p1 => [ | p' l hrec] p1 |> /#. qed.

  lemma wf_minf_in (sl:skip_list) : wf sl => minf \in sl.
  proof. smt(is_path_mem). qed.

  lemma wf_pinf_in (sl:skip_list) : wf sl => pinf \in sl.
  proof. 
    move=> [] |> _ _ _ l ^ /is_path_mem h /is_path_last h' _.
    case: l h h'; 1: by rewrite /= pinf_minf.
    move=> p l; rewrite lastI => /(_ pinf) => h heq; apply h.
    by rewrite -heq mem_rcons.
  qed.

  lemma path_empty : path empty = [pinf].
  proof. apply: is_path_path is_path_empty. qed.

  lemma is_path_pinf sl p1 p2 l1 l2: 
    wf sl => 
    is_path sl p1 l1 p2 =>
    is_path sl p1 l2 pinf => 
    exists l, is_path sl p2 l pinf /\ l2 = l1 ++ l.
  proof. move=> hwf; elim : l1 p1 l2 => |> => [ | ??? []]; smt(wf_minf_in). qed.

  lemma is_path_with_data (sl:skip_list) p d p1 l p2 : 
    is_path sl p1 l p2 => 
    is_path sl.[p <- with_data sl.[p] d] p1 l p2.
  proof.
    elim: l p1 => [ | p' l hrec] /= p1. 
    + by move=> |>; rewrite mem_setE => ->.
    rewrite /lt /= !set_with_data_forward !set_with_data_key !mem_setE => />.
    move=> 4?; apply hrec.
  qed.

  op path_btw (sl:skip_list) p1 p2 =
    choiceb (fun (l : ptr list) => is_path sl p1 l p2) [].

  lemma is_path_path_bth (sl : skip_list) p1 l p2 : 
    is_path sl p1 l p2 => path_btw sl p1 p2 = l.
  proof.
    apply (choiceb_uniq _ (fun l => is_path sl p1 l p2)) => /= ??; apply is_path_inj.
  qed.

  lemma is_path_imp (sl sl':skip_list) p1 l p2 :
    (forall p, p \in p1 :: l =>
       (p \in sl => p \in sl') /\
       Key sl p = Key sl' p /\
       height sl p <= height sl' p /\
       (p <> p2 => next sl p = next sl' p)) =>
    is_path sl p1 l p2 => is_path sl' p1 l p2.
  proof. elim: l p1 => //= * |>; smt( is_path_lt EK.lt_trans EK.lt_nle). qed.

  lemma eq_is_path (sl sl':skip_list) p1 l p2 :
    (forall p, p \in p1 :: l =>
       p \in sl = p \in sl' /\
       Key sl p = Key sl' p /\
       height sl p = height sl' p /\
       ( p <> p2 => next sl p = next sl' p)) =>
    is_path sl p1 l p2 = is_path sl' p1 l p2.
  proof. smt(is_path_imp). qed.

  op in_path (sl : skip_list) (p:ptr) =
    p \in minf::path sl.

  op ltp sl p1 p2 = 
     in_path sl p1 /\ in_path sl p2 /\ EK.(<) (Key sl p1) (Key sl p2).

  op lep sl p1 p2 = 
     in_path sl p1 /\ in_path sl p2 /\ EK.(<=) (Key sl p1) (Key sl p2).

  lemma is_path_lep (sl : skip_list) p1 l p2 : 
    has_path sl minf pinf => Key sl pinf = Pinf => in_path sl p1 => is_path sl p1 l p2 =>
    lep sl p1 p2.
  proof. 
    move=> hwf hpinf hin1 his.
    have [l1 hpl1]:= in_path_is_path _ _ hwf hin1.
    have hpl2 := is_path_trans _ _ _ _ _ _ hpl1 his.
    have hin2 := is_path_in_path _ _ _ hwf hpinf hpl2.
    smt (is_path_lt).
  qed.

  lemma lep_is_path (sl : skip_list) p1 p2 : 
    has_path sl minf pinf =>  lep sl p1 p2 => exists l, is_path sl p1 l p2.
  proof.
    move=> hwf [hin1 [hin2 hle]].
    have hp := pathP _ hwf.
    have |> l21 l22 hpmp2 hpp2p heq := is_path_in _ _ _ _ _ hp hin2. 
    move: (hin1); rewrite /in_path heq -cat_cons mem_cat => -[] hin.
    + by have |> _ l _ ? _:= is_path_in _ _ _ _ _ hpmp2 hin; exists l.
    have |> l _ hpp2p1 _ _ := is_path_in _ _ _ _ p1 hpp2p _; 1: by rewrite /= hin.
    have := is_path_lt _ _ _ _ hpp2p1.
    case: (l = []) => [ ? ->>| ]; smt (is_path_mem EK.lt_nle).
  qed.

  lemma ltp_all (sl : skip_list) (p1 p2 : ptr) (P : ptr -> bool) :   
    has_path sl minf pinf => Key sl pinf = Pinf => 
    ltp sl p1 p2 => 
    (forall p, ltp sl p1 p => ltp sl p p2 => P p) => 
    exists l, is_path sl p1 (rcons l p2) p2 /\ all P l .
  proof.
    move=> hwf hpinf hlt hall.
    have [l hpl] := lep_is_path sl p1 p2 hwf _; 1: smt().
    case: l hpl; 1: smt(EK.lt_nle).
    move=> p' l'; rewrite lastI => hpl /=.
    have := is_path_last _ _ _ _ hpl; rewrite last_rcons => heq. 
    move: hpl; rewrite -heq => hpl.
    exists  (belast p' l'); split => //.
    apply/allP => p hin.
    case: hlt => hin1 [hin2 hlt].
    have [l1 hpl1] := in_path_is_path _ _ hwf hin1.
    have [l11 _ [hpl11 _]]:= is_path_in _ _ _ _ p hpl _; 1: by rewrite /= mem_rcons /= hin.
    have hpl1l11:= is_path_trans _ _ _ _ _ _ hpl1 hpl11.
    have hinp := is_path_in_path _ _ _ hwf hpinf hpl1l11.
    move=> {l1 l11 hpl1 hpl11 hpl1l11}.
    have [l1 l2 heq1 ]:= splitPr _ _ hin.
    have hrcons0: forall l (p':ptr), rcons l p' <> [] by case.
    move: hpl; rewrite heq1 rcons_cat /= -cat_rcons is_path_cat last_rcons => -[] /is_path_lt h1 /is_path_lt h2 /#.
  qed.

  lemma all_ltp (sl : skip_list) (p1 p2 : ptr) (P : ptr -> bool) :   
    has_path sl minf pinf => Key sl pinf = Pinf => in_path sl p1 =>
    (exists l, is_path sl p1 (rcons l p2) p2 /\ all P l) => 
    (ltp sl p1 p2 /\ forall p, ltp sl p1 p => ltp sl p p2 => P p).
  proof.
    move=> hwf hpinf hin [l [hpl hall]].
    have := is_path_lep sl p1 _ p2 hwf hpinf hin hpl.
    have := is_path_lt _ _ _ _ hpl.
    have -> /= ?? : rcons l p2 <> [] by case: (l).
    split; 1: smt().
    rewrite /ltp => |> p _ hinp hlt1 hinp2 hlt2.
    move/allP: hall; apply.
    have [l1 hpl1]:= lep_is_path sl p1 p hwf _; 1: smt().
    have [l2 hpl2]:= lep_is_path sl p p2 hwf _; 1: smt().
    have := is_path_lt _ _ _ _ hpl2.
    case: l2 hpl2; 1: smt(EK.lt_nle).
    move=> x2 l2; rewrite lastI => |> hpl2 _.
    have hpl' {hpl2} := is_path_trans _ _ _ _ _ _ hpl1 hpl2.
    have {hpl hpl'}:= is_path_inj  _ _ _ _ _ hpl hpl'.     
    rewrite -rcons_cat => /rconssI ->>.
    have := is_path_lt _ _ _ _ hpl1.
    case: l1 hpl1; 1: smt(EK.lt_nle).
    move=> x1 l1; rewrite lastI => /is_path_last -> _.
    by rewrite mem_cat mem_rcons last_rcons.
  qed.

  lemma is_path_bound p sl p1 l p2 : 
    is_path sl p1 l p2 => p \in l => Key sl p1 < Key sl p /\ Key sl p <= Key sl p2.
  proof.
    case: l => /> l ?? hlt _ hpl [->> | hin ];1: smt(is_path_lt).
    have [l1 l2 [ ]]:= is_path_in _ _ _ _ p hpl _; 1: by rewrite /= hin. 
    smt(is_path_lt EK.lt_trans EK.lt_nle).
  qed.
  
  lemma is_path_bound_ne p sl p1 l p2 : 
    is_path sl p1 l p2 => p \in l => p <> p2 => Key sl p1 < Key sl p /\ Key sl p < Key sl p2.
  proof. 
    case: l => /> l ?? hlt _ hpl [->> | hin ];1: smt(is_path_lt).
    have [l1 l2 [ ]]:= is_path_in _ _ _ _ p hpl _; 1: by rewrite /= hin. 
    smt(is_path_lt EK.lt_trans EK.lt_nle).
  qed.


  (* ************************************************************************* *)
  (* wf_ptr wf                                                                 *)

  lemma wf_ptr_with_data sl p d p1 : 
    wf_ptr sl p1 =>   
    wf_ptr sl.[p <- with_data sl.[p] d] p1.
  proof. 
    rewrite /wf_ptr => |> h1 h2. 
    rewrite !set_with_data_forward;
    smt(set_with_data_key set_with_data_forward is_path_with_data).  
  qed.

  lemma wf_with_data sl p d :
    wf sl => p <> minf => p <> pinf => 
    wf sl.[p <- with_data sl.[p] d].
  proof.
    smt(setE set_with_data_key set_with_data_forward is_path_with_data wf_ptr_with_data).
  qed.

  lemma path_with_data sl p d : 
    wf sl => p <> pinf =>
    path sl.[p <- with_data sl.[p] d] = path sl.
  proof.
    move=> hwf hne.
    by apply/is_path_path/is_path_with_data/pathP/wf_has_path.
  qed.
    
  (* ************************************************************************* *)
  (* hsl and dsl                                                               *)

  op get_ptr (sl:skip_list) (k:ekey) =
     choiceb (fun p => p \in minf::path sl /\ Key sl p = k) minf.

  lemma Key_inj sl p1 p2 : 
    wf sl => 
    p1 \in minf::path sl =>
    p2 \in minf::path sl => 
    Key sl p1 = Key sl p2 => p1 = p2.
  proof.
    move=> hwf.
    case : (p1 = p2) => // hne hin1 hin2.
    suff : lt sl p1 p2 \/ lt sl p2 p1 by smt(EK.lt_nle).
    have hp := pathP sl (wf_has_path sl hwf).
    have |> l1 l2 hp1 hp2 heq := is_path_in _ _ _ _ p1 hp hin1.
    move: hin2; rewrite heq mem_cat => |>.
    move=> [ ->> | [ ] hin2 ];1: smt(is_path_lt).
    + have := is_path_in _ _ _ _ p2 hp1.
      by rewrite /= hin2 /= => |> l1' l2' ? hp2' ->>; smt(is_path_lt).
    have := is_path_in _ _ _ _ p2 hp2.
    by rewrite /= hin2 /= => |> l1' l2' ? hp2' ->>; smt(is_path_lt).
  qed.

  lemma get_ptr_in sl p : 
    wf sl => 
    p \in minf::path sl => 
    get_ptr sl (Key sl p) = p.
  proof. 
    move=> hwf hin; apply choiceb_uniq => //.
    move=> p1 p2 /=.
    have /# := (Key_inj sl p1 p2 hwf).
  qed.   
 
  lemma get_ptr_with_data sl p d k : 
    wf sl => p <> pinf =>
    get_ptr sl.[p <- with_data sl.[p] d] k = get_ptr sl k.
  proof.
    move=> hwf hne; apply eq_choice => p1 /=.
    by rewrite path_with_data // set_with_data_key.
  qed.

  lemma bindingsP (f:node -> 'a) (sl:skip_list) k : 
    wf sl =>  
    let bd = bindings f sl in
    bd.[k] = if exists p, p \in minf::path sl /\ Key sl p = k then Some (f sl.[get_ptr sl k])
             else None.
  proof.
    pose l := minf::path sl.
    move => /= hwf; rewrite /bindings ofassoc_get.
    rewrite -/l.
    pose F := (fun (p : ptr) => let n = sl.[p] in (n.`key, f n)).
    case: (exists (p : ptr), (p \in l) /\ Key sl p = k); last first.
    + case: (assoc (map F l) k = None) => //.
      move=> /assocTP /=.
      by rewrite -map_comp /(\o) => /mapP [p] /= [] ? ->; exists p.
    move=> hex.
    have /= {hex}:= choicebP _ minf hex; rewrite -/(get_ptr sl k) => |>.
    move=> hin {1} <-. 
    move: (get_ptr sl k) hin => p hin.
    apply mem_assoc_uniq; 2: by apply mapP; exists p => /=.
    rewrite -map_comp /(\o) /=.
    apply map_inj_in_uniq; 2: by apply path_uniq.
    rewrite /l /F => p1 p2 /=; apply (Key_inj _ p1 p2 hwf).
  qed.

  lemma bindingsP_in (f:node -> 'a) (sl:skip_list) p : 
    wf sl => p \in minf:: path sl => (bindings f sl).[Key sl p] = Some (f sl.[p]).
  proof.
    move => /= hwf hin.
    have /= -> := bindingsP f sl (Key sl p) hwf.
    have -> /= : exists (p0 : ptr),
                (p0 = minf \/ (p0 \in path sl)) /\ Key sl p0 = Key sl p.
    + by exists p.
    by rewrite get_ptr_in.
  qed.

  lemma hslP_in_height (sl:skip_list) p : 
    wf sl => p \in (minf::path sl) => 
    (hsl sl).[Key sl p] = height sl p.
  proof.
    by move=> hwf hin; have /= -> := bindingsP_in (fun (n : node) => size n.`forward) sl p hwf hin.
  qed.

  lemma hslP_in (sl:skip_list) p : 
    wf sl => p \in (minf::path sl) => 
    Key sl p \in (hsl sl).
  proof.
    move=> hwf hin; rewrite domE.
    have /= -> //:= bindingsP_in (fun (n : node) => size n.`forward) sl p hwf hin.
  qed.

  lemma hslP (sl:skip_list) k : 
    wf sl => 
    SmtMap."_.[_]" (hsl sl) k =
       if exists p, p \in minf::path sl /\ Key sl p = k then Some (height sl (get_ptr sl k))
       else None.
  proof. by move=> hwf; apply (bindingsP (fun n => size n.`forward) sl k). qed.

  lemma hslE_in (sl:skip_list) p : 
    wf sl => 
    p \in minf:: path sl => 
    SmtMap."_.[_]" (hsl sl) (Key sl p) = Some (height sl p).
  proof. apply (bindingsP_in (fun (n : node) => size n.`forward)). qed.

  lemma dslP (sl:skip_list) k : 
    wf sl => 
    (dsl sl).[k] = 
       if exists p, p \in minf::path sl /\ Key sl p = k then Some (sl.[get_ptr sl k].`data)
       else None.
  proof. by move=> hwf; apply (bindingsP (fun n => n.`data) sl k). qed.

  lemma dslE_in (sl:skip_list) p : 
    wf sl => 
    p \in minf:: path sl => 
    (dsl sl).[Key sl p] = Some (sl.[p].`data).
  proof. apply (bindingsP_in (fun (n : node) => n.`data)). qed.

  lemma hsl_with_data (sl:skip_list) p d :
    wf sl => p \in path sl => p <> pinf =>
    hsl (sl.[p <- with_data sl.[p] d]) = hsl sl.
  proof.
    move=> hwf hin hnep.
    have hwf' := wf_with_data _ _ d hwf _ hnep.
    + by have /# := is_path_bound _ _ _ _ _ (pathP sl (wf_has_path sl hwf)) hin. 
    apply fmap_eqP => k.
    rewrite (hslP _ _ hwf) (hslP _ _ hwf').
    rewrite path_with_data // get_ptr_with_data // set_with_data_forward; congr. 
    smt(set_with_data_key).
  qed.

  lemma dsl_with_data (sl:skip_list) p d :
    wf sl => p \in path sl => p <> pinf =>
    dsl (sl.[p <- with_data sl.[p] d]) = (dsl sl).[Key sl p <- d].
  proof.
    move=> hwf hin hne.
    have hwf' := wf_with_data _ _ d hwf _ hne.
    + by have /# := is_path_bound _ _ _ _ _ (pathP sl (wf_has_path sl hwf)) hin. 
    apply fmap_eqP => k.
    rewrite get_setE (dslP _ _ hwf) (dslP _ _ hwf').
    rewrite path_with_data // get_ptr_with_data //.
    case: (k = Key sl p) => [->> | hneq].
    + by rewrite get_ptr_in //; smt(get_setE set_with_data_key).
    rewrite setE; case: (get_ptr sl k = p); 2: smt(set_with_data_key).
    move=> heq.
    have -> : (exists (p0 : ptr), (p0 = minf \/ (p0 \in path sl)) /\
               (sl.[p <- with_data sl.[p] d].[p0]).`key = k) <=>
              (exists (p0 : ptr), (p0 = minf \/ (p0 \in path sl)) /\ (sl.[p0]).`key = k).
    + smt(set_with_data_key).
    case: (exists (p0 : ptr), (p0 = minf \/ (p0 \in path sl)) /\ (sl.[p0]).`key = k) => />.
    by move=> p' hin' <<-; have := get_ptr_in _ p' hwf hin'; rewrite heq => <<-. 
  qed.

  (* ************************************************************************* *)
  (* Walk-back                                                                 *)

  lemma walk_back_nil (sl:hsl) ch : walk_back sl ch [] = ch.
  proof. done. qed.

  lemma walk_back_cons (sl:hsl) ch k l :
    walk_back sl ch (k::l) = walk_back sl (walk_back_step sl ch k) l.
  proof. done. qed.
   
  lemma walk_back_cat (sl:hsl) ch l1 l2 : 
    walk_back sl ch (l1++l2) = walk_back sl (walk_back sl ch l1) l2.
  proof. by rewrite /walk_back foldl_cat. qed.

  lemma walk_backD sl ch l n :
    (walk_back sl ch l).`1 + n = (walk_back sl (ch.`1+n,ch.`2) l).`1.
  proof. rewrite /walk_back; elim: l ch => //= /#. qed.

  lemma walk_back_forward sl p1 p2 l c h: 
    is_path sl p1 l p2 => 
    all (fun p => (hsl sl).[Key sl p]  <= h) l =>
    walk_back (hsl sl) (c, h) (rev (map (Key sl) l)) = (c,h).
  proof.
    elim/last_ind l p2 => // l p hrec p2.
    rewrite -cats1 is_path_cat map_cat rev_cat all_cat=> |> hp1 hlt h0ei hin hall hei.
    rewrite rev_cons rev_nil /= walk_back_cons /walk_back_step /= hei /=. 
    apply: hrec hp1 hall.
  qed.
   
  (* ************************************************************************* *)
  (* Functional correctness + cost of SL.find                                  *)

  hoare find_spec sl_ k_ : SL.find : 
    wf sl /\ sl = sl_ /\ k = k_ ==> res = ((dsl sl_).[K k_], path_len (hsl sl_) (K k_)).
  proof.
    proc.
    rewrite /path_len /=.
    while ( wf sl /\ 
            -1 <= h < height sl pos /\ pos <> pinf /\ sl.[pos].`key <= K k /\
            nexts = (sl.[pos]).`forward /\
            (h = -1 => K k < sl.[next sl pos].`key) /\
            exists l1 l2, 
               is_path sl minf l1 pos /\ 
               is_path sl pos l2 pinf /\
               (forall p, p \in l2 => h < height sl p - 1 => K k < Key sl p) /\
               cst = (walk_back (hsl sl) (0,h) (rev (map (Key sl) (minf::l1)))).`1).
    + auto => |> &hr.
      move: (sl{hr}) (k{hr}) (h{hr}) (pos{hr}) => {&hr sl_ k_} sl k h pos.
      move=> hwf hm1h hhei hpinf hposk hkm1 l1 l2 hpath1 hpath2 hkey h0h.
      have h0hei : 0 <= h < height sl pos by done.       
      have [? /(_ h h0hei) |> hheif l21 hp21 hall] := wf_ptr_last _ _ _ hwf hpath1.
      have |> l22 hp22 heq2 := is_path_pinf _ _ _ _ _ hwf hp21 hpath2.
      split.
      + move=> hK; rewrite andbA; split; 1: smt().
        exists l1 l2; rewrite hpath1 hpath2 /= walk_backD.
        split.
        + move=> p hp; have := hkey _ hp.
          move: hp; rewrite heq2 mem_cat mem_rcons => -[]; 1: smt(allP).
          move=> hin.
          have |> ??:= is_path_in _ _ _ _ p hp22 _; 1: by rewrite /= hin.
          by move=> /is_path_lt; smt(EK.lt_trans).
        rewrite -/(rev (map (Key sl) (minf::l1))). 
        pose r := rev _.
        have heq : r = sl.[pos].`key :: drop 1 r.
        + by rewrite /r lastI -(is_path_last _ _ _ _ hpath1) map_rcons rev_rcons drop_cons /= drop0.
        rewrite /= heq !walk_back_cons /walk_back_step /=.
        by rewrite (hslP_in_height sl pos hwf _) 2:/#; apply (is_path_in_path _ _ _ (wf_has_path sl hwf) (wf_pinf _ hwf) hpath1).
      move=> hK; rewrite !andbA; split; 1: smt(EK.lt_nle).
      exists (l1 ++ rcons l21 (sl.[pos]).`forward.[h]) l22.
      split; 1: by apply: is_path_trans hpath1 hp21.
      rewrite hp22 /=; split.
      + by move=> p hp; have // := hkey p _; rewrite heq2 mem_cat hp.
      rewrite -/(rev (map (Key sl) (minf::l1 ++ rcons l21 (sl.[pos]).`forward.[h]))). 
      rewrite map_cat rev_cat walk_back_cat map_rcons rev_rcons walk_back_cons walk_backD.
      rewrite /walk_back_step /=.
      have ? := hkey (Forward sl pos).[h] _; 1: by rewrite heq2 mem_cat mem_rcons /=.
      have -> := hslP_in_height _ (Forward sl pos).[h] hwf _.
      + apply : (is_path_in_path sl (l1 ++ rcons l21 (Forward sl pos).[h])). + by apply wf_has_path. + by apply wf_pinf.
        by apply: is_path_trans hpath1 hp21.
      have heqh: h = height sl (Forward sl pos).[h] - 1 by smt().
      have -> /= : !(height sl (Forward sl pos).[h] <= h) by smt().
      rewrite -heqh.
      have -> : height sl (Forward sl pos).[h] - h = 1 by rewrite {2}heqh; ring.
      move: hp21; rewrite -cats1 is_path_cat => -[hp21 _].
      have -> : Key sl (Forward sl pos).[h] <> Minf.
      + have [] |> _ := wf_ptr_last _ _ _ hwf hpath1.
        move=> /(_ h _); 1: smt().
        by move=> |> _ l; rewrite -cats1 is_path_cat; smt(EK.lt_trans EK.lt_nle).
      have -> //:= walk_back_forward _ _ _ _ 1 h hp21.
      apply/allP => p' hp'; move/allP: hall => /(_ _ hp') /=.
      rewrite hslP_in_height //.
      have hplast: is_path sl minf (l1 ++ l21) (last pos l21).
      + by apply: is_path_trans hpath1 hp21.
      have |> := is_path_in _ _ _ _ p' hplast _; 1: by rewrite /= mem_cat hp'.
      move=> lp' _ hpp' _ _.
      apply: is_path_in_path (wf_has_path _ hwf) (wf_pinf _ hwf) hpp'.
    (* end loop body *)
    auto => |> hwf; split.
    + rewrite !andbA; split; 1: smt().
      exists [] (path sl_); rewrite /= pathP 1:wf_has_path //=; split; [by apply wf_minf_in | split].
      + move=> p hp; case: (hwf) => |> _ _ _ _ /is_path_path <<- /(_ p).
        by rewrite hp /= => -[] |>; smt(size_ge0 size_mkarray).
      rewrite /rev /= walk_back_cons /walk_back_step /=.
      by rewrite hslP_in_height // /#.
    move=> h pos 4? hle; have ->> /= ?: h = -1 by smt().
    move=> l1 l2 hpl1 hpl2 hinl2; split.
    + rewrite dslP 1://.
      case (K k_ = sl_.[pos].`key) => heq; 1: smt(is_path_in_path get_ptr_in).
      case: (exists (p : ptr), (p = minf \/ (p \in path sl_)) /\ Key sl_ p = K k_) => //.
      move=> [p [hpin heqp]]; case: hpin; 1: smt().
      have /is_path_path -> := is_path_trans _ _ _ _ _ _ hpl1 hpl2.
      rewrite mem_cat=> -[] hin.
      + have [? l12 [# _ /is_path_lt]]:= is_path_in _ _ _ _ p hpl1 _; 1: by rewrite /= hin.
        smt(EK.lt_nle).
      have [l21 ? [# /is_path_lt]]:= is_path_in _ _ _ _ p hpl2 _; 1: by rewrite /= hin.
      smt(EK.lt_nle).
    rewrite /predecessors /=.
    have -> : elems (hsl sl_) = rev (map (Key sl_) (minf::path sl_)).    
    + rewrite /elems; congr; apply (eq_sorted EK.(<=)).
      + by apply EK.le_trans. + smt(EK.lt_nle).
      + by apply/sort_sorted/EK.le_total.
      + have := is_path_sorted pinf _ _ _ (pathP _ (wf_has_path _ hwf)).
        by apply sorted_map => />; rewrite /(<=) => />.
      apply/perm_sortl/uniq_perm_eq; 1: by apply uniq_elems.
      + apply map_inj_in_uniq; 1: by move=> 2?; apply Key_inj.
        by apply path_uniq.
      move=> p; rewrite -memE fdomP mapP hslP // /#.
    have /is_path_path -> := is_path_trans _ _ _ _ _ _ hpl1 hpl2.
    rewrite -cat_cons map_cat rev_cat find_cat.
    have -> /= : ! has (fun (k' : ekey) => k' <= K k_) (rev (map (Key sl_) l2)).
    + apply/negP => /hasP [k' [] /=]; rewrite mem_rev => /mapP [p [hp ->> ]].
      rewrite -lt_nle.
      have |> l21 ? hp21 _ _ := is_path_in _ _ _ _ p hpl2 _; 1: by rewrite /= hp.
      by have /# := wf_ptr_last _ (l1 ++ l21) p hwf _; 1: by apply: is_path_trans hpl1 hp21.
    have -> /= : find (fun (k' : ekey) => k' <= K k_) (rev (Key sl_ minf :: map (Key sl_) l1)) = 0.
    + have <- := map_cons (Key sl_) minf l1; rewrite -map_rev.
      pose r := rev _; have -> : r = pos :: drop 1 r.
      + by rewrite /r lastI -(is_path_last _ _ _ _ hpl1) rev_rcons drop_cons /= drop0.
      by rewrite /= hle.
    by rewrite drop_cat /= drop0.
  qed.
  
  phoare find_spec_ll sl_ k_ : 
    [ SL.find : 
      wf sl /\ sl = sl_ /\ k = k_ 
      ==> 
      res = ((dsl sl_).[K k_], path_len (hsl sl_) (K k_))
    ] = 1%r.
  proof.
    conseq (:  wf sl ==> true) ( find_spec sl_ k_) => //.
    proc.
    while ( wf sl /\ 
            -1 <= h < height sl pos /\ pos <> pinf /\
            nexts = Forward sl pos /\
            exists l1 l2, is_path sl minf l1 pos /\ is_path sl pos l2 pinf) 
          (* Variant *)
          (size (path_btw sl pos pinf) + h).
    + move=> z; auto => |> &hr; move: (sl{hr}) (h{hr}) (pos{hr}) (k{hr}) => sl h pos k.
      move=> hwf _ hhei hpinf l1 l2 hpl1 hpl2 h0h.
      have h0hei : 0 <= h < height sl pos by done.       
      have [? /(_ h h0hei) |> hheif l21 hp21 hall] := wf_ptr_last _ _ _ hwf hpl1.
      have |> l22 hp22 heq2 := is_path_pinf _ _ _ _ _ hwf hp21 hpl2.
      split; 1: smt().
      move=> hK; rewrite andbA; split.
      + split; 1: smt().
        exists (l1 ++ rcons l21 (Forward sl pos).[h]) l22; split => //.
        by apply: is_path_trans hpl1 hp21.
      rewrite (is_path_path_bth _ _ _ _ hpl2) (is_path_path_bth _ _ _ _ hp22) heq2 size_cat.
      smt(List.size_ge0 List.size_rcons).
    auto => |> &hr; move: (sl{hr}) => sl {&hr} hwf.
    split. 
    + rewrite !andbA; split; 1: smt (size_ge0).
      exists [] (path sl); split; 1: by apply (wf_minf_in _ hwf).
      by rewrite /= pathP 1:wf_has_path //; case: hwf => |>.
    move=> h pos _ _ hpinf _ l2 _ hpl2.
    rewrite ( is_path_path_bth _ _ _ _ hpl2).
    have := is_path_lt _ _ _ _ hpl2.
    smt(List.size_ge0).
  qed.

  lemma forward_in (sl : skip_list) (l : ptr list) (pos : ptr) :
    wf sl => 
    is_path sl minf l pos => forall (p : ptr), p \in minf :: l => 
    forall h, 0 <= h < height sl p => 
    (Forward sl p).[h] \in sl.
  proof.
    move=> hwf hpl p hin h hh.
    have [hh1 hh2]:= is_path_wf_ptr _ _ _ hwf hpl _ hin.
    have [ _ [l' [h1 _]]] := hh2 h hh.
    have [l1 l2 [# h3 _ _]]:= is_path_in _ _ _ _ _ hpl hin.
    have /is_path_mem := is_path_trans _ _ _ _ _ _ h3 h1.
    by apply; rewrite /= mem_cat mem_rcons.
  qed.

  lemma forward_in_path (sl : skip_list) (l : ptr list) (pos : ptr) :
    wf sl => 
    is_path sl minf l pos => forall (p : ptr), p \in minf :: l => 
    forall h, 0 <= h < height sl p => 
    in_path sl (Forward sl p).[h].
  proof.
    move=> hwf hpl p hin h hh.
    have [hh1 hh2]:= is_path_wf_ptr _ _ _ hwf hpl _ hin.
    have [ _ [l' [h1 _]]] := hh2 h hh.
    have [l1 l2 [# h3 _ _]]:= is_path_in _ _ _ _ _ hpl hin.
    have := is_path_trans _ _ _ _ _ _ h3 h1.
    by apply is_path_in_path; [apply wf_has_path | apply wf_pinf]. 
  qed.

  lemma wf_ptr_between sl p h p': 
    wf sl => in_path sl p => 0 <= h < height sl p => 
    in_path sl p' => Key sl p < Key sl p' < Key sl (Forward sl p).[h] =>
    height sl p' <= h.
  proof.
    move=> hwf hin hhei hin' hK; have hhas := wf_has_path sl hwf; have hpinf := wf_pinf sl hwf.
    have [_ /(_ h hhei) [_ [l [hisp hall]]]]:= is_path_wf_ptr sl (path sl) pinf hwf (pathP sl hhas) _ hin.
    have [l1 hpl1]:= lep_is_path sl p p' hhas _; 1: smt().
    have [lp hlp]:= in_path_is_path _ _ hhas hin.
    have hlsp := is_path_trans _ _ _ _ _ _ hlp hisp.
    have hins := is_path_in_path sl _ (Forward sl p).[h] hhas hpinf hlsp.
    have [l2 hpl2]:= lep_is_path _ p' (Forward sl p).[h] hhas _; 1: smt().
    have := is_path_lt _ _ _ _ hpl2.
    case: l2 hpl2; 1: by move=> _ /= ->>; smt(EK.lt_nle).
    move=> x2 l2; rewrite lastI => hpl2 _.
    have := is_path_lt _ _ _ _ hpl1.
    case: l1 hpl1; 1: by move=> _ /= ->>; smt(EK.lt_nle).
    move=> x1 l1; rewrite lastI => hpl1 _.
    have := is_path_last _ _ _ _ hpl1.
    have := is_path_last _ _ _ _ hpl2.
    rewrite !last_rcons => heq2 heq1.
    move: hpl1 hpl2; rewrite -heq1 -heq2 => hpl1 hpl2.
    have hisp' := is_path_trans _ _ _ _ _ _ hpl1 hpl2.
    have := is_path_inj _ _ _ _ _ hisp hisp'.
    rewrite -rcons_cat => /rconssI ->>.    
    by move/allP: hall; apply; rewrite mem_cat mem_rcons.
  qed.

  lemma is_path_in_cons sl p1 l p2 : is_path sl p1 l p2 => p2 \in p1::l.
  proof. move=> /is_path_last; elim: l p1 => //=; smt(last_cons). qed.

  hoare insert_h_spec sl_ k_ d_ hk_: SL.insert_h :
    wf sl /\ (sl,k,d,hk) = (sl_, k_, d_, hk_) /\ 0 <= hk 
    ==> 
    wf res /\ dsl res = (dsl sl_).[K k_ <- d_] /\ 
    hsl res = 
      let hsl_ = hsl sl_ in
      if K k_ \in hsl_ then hsl_
      else hsl_.[Minf <- max hsl_.[Minf] (hk_ + 1)].[K k_ <- hk_ + 1].
  proof.
    proc.
    seq 5 :
        ( wf sl /\ k = k_ /\ sl = sl_ /\ d = d_ /\ hk = hk_ /\ 0 <= hk /\
          stk.[0] = pos /\
          size stk = height sl minf /\
          pos <> pinf /\
          Key sl pos <= K k < Key sl (next sl pos) /\
          exists l1 l2,
            is_path sl minf l1 pos /\ 
            is_path sl pos l2 pinf /\
            (forall p h',
               0 <= h' < height sl p =>  
               p \in (minf::l1) =>
               K k < Key sl (Forward sl p).[h'] =>
               stk.[h'] = p) /\
            (forall h',
              0 <= h' < size stk =>
              stk.[h'] \in (minf::l1) /\
              h' < height sl stk.[h'] /\
              Key sl stk.[h'] <= Key sl stk.[0] <= K k < Key sl (Forward sl stk.[h']).[h'])).
     + while ( (wf sl /\
               -1 <= h < height sl pos /\ pos <> pinf /\
               size stk = height sl minf /\
               nexts = Forward sl pos /\
               Key sl pos <= K k /\
               (h = -1 => K k < Key sl (next sl pos))) /\
               exists l1 l2, 
                 is_path sl minf l1 pos /\ 
                 is_path sl pos l2 pinf /\
                 (forall p h',
                   h < h' < height sl p =>   (* h' need to be less than height sl p *) 
                   p \in (minf::l1) =>
                   K k < Key sl (Forward sl p).[h'] =>
                   stk.[h'] = p) /\
                 (forall p, p \in l2 => h < height sl p - 1 => K k < Key sl p) /\ 
                 (forall h', h < h' < size stk => Key sl stk.[h'] <= Key sl pos) /\ 
                 (forall h',
                  h < h' < size stk =>
                   stk.[h'] \in (minf::l1) /\
                   h' < height sl stk.[h'] /\
                   Key sl stk.[h'] <= K k < Key sl (Forward sl stk.[h']).[h'])).
       + auto => |> &hr.
         move: (sl{hr}) (stk{hr}) (k{hr}) (pos{hr}) (h{hr}) => {&hr} sl stk k pos h.
         move => hwf hhl hhu ???? l1 l2 hlp1 hlp2  hfull hstk hdecr hlast *.
         have hp := pathP sl (wf_has_path sl hwf).
         have wf_ptr_all: forall p, p \in minf::path sl => wf_ptr sl p by smt(is_path_wf_ptr).
         have wfpos:= wf_ptr_last sl l1 pos hwf hlp1.
         split.
         + move=> hK; rewrite andbA; split; 1: smt(size_set).
           exists l1 l2; rewrite hlp1 hlp2 /=.
           split.
           + move=> p h'. rewrite get_set_if /=.
             move => hh' p_in_left k_fwd.
             have wfp: wf_ptr sl p by smt(is_path_wf_ptr).
             have -> /=: (0 <= h && h < size stk) by smt().
             case (h < h') => [|*]; 1: by smt().
             have ->> /=: h' = h by smt().
             apply contraT => neq.
             have /# := wf_ptr_between sl p h pos hwf _ _ _ _.
             + rewrite /in_path (is_path_path sl (l1 ++ l2)).
               + by apply: is_path_trans hlp1 hlp2.
               smt(mem_cat).
             + smt().
             + by have /# := (is_path_in_path sl l1 pos). 
             split; 2: smt(EK.lt_trans).
             have := is_path_bound_ne p sl minf l1 pos hlp1. 
             by have /# := is_path_lt sl minf l1 pos hlp1.
           split.
           + move=> p hpl2 hh.
             case: (wfpos) => h1 /(_ h _) // [h2 [l21]] [h3 /allP /= h4]. 
             have [l22 [hl22 ->>]]:= is_path_pinf sl pos _ _ _ hwf h3 hlp2.
             move: hpl2; rewrite mem_cat => -[]; 2: smt(is_path_bound EK.lt_trans).
             by rewrite mem_rcons => -[ -> // | /#].
           split; 1: by move=> h'; rewrite size_set !get_set_if /= /#.        
           move=> h'; rewrite size_set !get_set_if /=.
           have -> /=: (0 <= h && h < size stk) by smt().
           by case: (h' = h) => [->> | /#]; smt (is_path_in_cons).
         move=> hK.
         have hle : Key sl (Forward sl pos).[h] <= K k by smt(EK.le_total).
         rewrite andbA; split; 1: smt().
         case: (wfpos) => h1 /(_ h _) // [h2 [l21]] [h3 /allP /= h4]. 
         have [l22 [hl22 ->>]]:= is_path_pinf sl pos _ _ _ hwf h3 hlp2.
         exists (l1 ++ rcons l21 (Forward sl pos).[h]) l22.
         split; 1: by apply: is_path_trans hlp1 h3.
         rewrite hl22 /=; split.         
         + move=> p h' hh'.
           rewrite mem_cat orbA => -[/#|]. 
           rewrite mem_rcons /= => -[ ->> ? | /#].
           have := hstk (Forward sl pos).[h].
           by rewrite mem_cat mem_rcons /= /#. 
         split; 1: smt(mem_cat).
         split; 1: smt(EK.le_trans is_path_bound mem_rcons).
         smt(mem_cat).
       auto => |> hwf hhk.
       have hp := pathP sl_ (wf_has_path sl_ hwf). rewrite !size_map.
       have wf_ptr_all : forall p, p \in minf::path sl_ => wf_ptr sl_ p. smt(is_path_wf_ptr).
       split.
       + split; 1:smt().
         by exists [] (path sl_); smt().
       move => h pos stk ? ?. have -> /=: h = -1 by smt().
       move => 5? l1 l2 hlp1 hlp2 hfull hord hlast.
       have // pos_in_l1: pos = minf \/ (pos \in l1).
       + have:=is_path_last _ _ _ _ (hlp1);
         move: {hlast hfull hlp1}. elim: l1 minf;
         by smt(last_cons).
       have /# : stk.[0] = pos.
       apply hfull => //. 
       have /# := wf_ptr_all pos _.
       by apply: is_path_in_path hlp1 => /#.


     (* update *)
     if. 
     + auto => |> &hr hwf 2? pos_pinf 2? l1 l2 hpminfpos 3? heq.
       rewrite (wf_with_data sl_ stk{hr}.[0] d_ hwf _ pos_pinf) /=; 1: smt().
       have hin := is_path_in_path _ _ _ (wf_has_path _ hwf) (wf_pinf _ hwf) hpminfpos.
       case: (hin) => [/# | ?].   
       by rewrite hsl_with_data // dsl_with_data //= heq (hslP_in _ _ hwf hin). 
     wp.
     while 
       (0 <= h /\ size fwk = hk + 1 /\ h <= size stk /\ h <= size fwk /\
        (forall h', 0 <= h' < size stk =>
          stk.[h'] \in sl_ /\ h' < height sl_ stk.[h']) /\
        (forall h', 0 <= h' < size fwk =>
          fwk.[h'] = if h' < h then (Forward sl_ stk.[h']).[h'] else pinf) /\
        (forall h', 0 <= h' < h =>
          (Forward sl stk.[h']).[h'] = pk) /\
        (forall p h', !(0 <= h' < h /\ stk.[h'] = p) =>
          (Forward sl p).[h'] = (Forward sl_ p).[h']) /\
        (forall p,
          (p \in sl_ = p \in sl) /\
          Data sl p = Data sl_ p /\
          Key sl p = Key sl_ p /\
          height sl p = height sl_ p)
      ).
     + by auto => |> &hr; smt(get_set_if setE size_set mem_setE).
     auto => |> &hr.
     move:  (stk{hr}) sl_ k_ d_ hk_ => {&hr} stk sl k d hk.
     move=> hwf ? stksz pospinf hK  hKnext l1 l2 hpl1 hpl2 hfull hlast ?.
     split; 1: smt(offunE size_offun is_path_mem).
     have heqpath : path sl = l1 ++ l2.
     + apply/is_path_path; apply:is_path_trans hpl1 hpl2.
     move=> fwk h0 sl1 ex h0ge0 sz_fwk a b.
     have ->: h0 = min (size stk) (size fwk) by smt().
     move: {h0ge0 a b ex}. move: {h0}.
     move=> _ fwk_iv fwd_new fwd_old sl_eqstruct.
     pose sl2 := sl1.[_ <- _].
     pose UpdMinf := offun _.
     have hfresh_not_in := fresh_ptrP sl.
     have minf_in := wf_minf_in _ hwf.
     have minf_ne_fresh : minf <> fresh_ptr sl.
     + by apply /negP => h; move: hfresh_not_in; rewrite -h.
     rewrite setE minf_ne_fresh /=.
     have hsz_minf : height sl1 minf = size stk. move: (sl_eqstruct minf) => /#.
     pose sl3 := set_minf sl2 (UpdMinf (max (size stk) (size fwk))).
     suff : 
       wf sl3 /\
       dsl sl3 = (dsl sl).[K k <- d] /\
       hsl sl3 =
         if K k \in hsl sl then hsl sl
         else (hsl sl).[Minf <- max (hsl sl).[Minf] (size fwk)].[K k <- size fwk].
     + move=> h; split; 1: smt().
       move=> ?; have -> // : sl2 = sl3.
       apply mem_eqP => p; rewrite !M.get_setE.
       case: (p = minf) => [->> | //].
       rewrite minf_ne_fresh /=.
       case _: (get sl1 minf) => [/# | [kn dn fn] hn].
       do 2! congr; 1,2: smt().
       apply arrayP.
       have hsz : size fn = size (UpdMinf (max (size stk) (size fwk))) by rewrite /UpdMinf size_offun /#.
       rewrite hsz /= => i; rewrite /UpdMinf size_offun => hi.
       by rewrite offunE 1:/# /= setE minf_ne_fresh /= /#.
     + by smt().

     have sl3_in : forall p, p \in sl3 <=> (p \in sl \/ p = fresh_ptr sl) by smt(mem_setE).

     have height_minf: height sl3 minf = max (size stk) (size fwk).
     + by rewrite setE /= /UpdMinf size_offun; smt(size_ge0).
     have height_fresh: height sl3 (fresh_ptr sl) = size fwk.
     + by rewrite !setE /#.
     have height_retained: forall p,
       p <> minf => p <> fresh_ptr sl =>
       height sl3 p = height sl p.
     + by move => *; rewrite !setE /#.

     have fresh_mem: fresh_ptr sl \in sl3. by smt(mem_setE).

     have key_retained: forall p, p <> fresh_ptr sl => Key sl3 p = Key sl p by smt(setE).
     have key_fresh : Key sl3 (fresh_ptr sl) = K k by smt (setE).
     have fwd_retained: forall p h,
       p <> fresh_ptr sl =>
       (p = stk.[h] => min (size fwk) (size stk) <= h) =>
       0 <= h < height sl p =>
       (Forward sl3 p).[h] = (Forward sl p).[h].
     + by smt(setE offunE).
     have fwd_fresh1: forall h, 0 <= h < min (size stk) (size fwk) =>
       (Forward sl3 stk.[h]).[h] = fresh_ptr sl. by smt(setE offunE).
     have fwd_fresh2 : forall h,
       size stk <= h < max (size stk) (size fwk) =>
       (Forward sl3 minf).[h] = fresh_ptr sl by smt(setE offunE).
     have fwd_new1: forall h,
       0 <= h < min (size stk) (size fwk) =>
       (Forward sl3 (fresh_ptr sl)).[h] = (Forward sl stk.[h]).[h] by smt(setE).
     have fwd_new2: forall h,
       min (size stk) (size fwk) <= h < size fwk =>
       (Forward sl3 (fresh_ptr sl)).[h] = pinf by smt(setE).

     have stk0_ne_fresh: stk.[0] <> fresh_ptr sl by smt(is_path_mem).
     have fresh_ne_l1: ! (fresh_ptr sl \in l1). smt(is_path_mem).
     have fresh_ne_l2: ! (fresh_ptr sl \in l2). smt(is_path_mem).
     have fresh_ne_sl: ! (fresh_ptr sl \in path sl). smt(mem_cat).
     have wf_ptr_minf: wf_ptr sl minf. by smt(is_path_wf_ptr).
     have minf_ne_l1: ! (minf \in l1). by smt(is_path_uniq).
     have minf_ne_l2: ! (minf \in l2). by smt(is_path_bound EK.lt_nle).
     have pinf_ne_l1: ! (pinf \in l1). by smt(is_path_bound EK.lt_nle).
     have stkh_ne_l2: forall h, 0 <= h < size stk => ! (stk.[h] \in l2). smt(is_path_bound EK.lt_nle).
     have mem_l1: forall p, p \in l1 => p \in sl by smt(is_path_mem).
     have mem_l2: forall p, p \in l2 => p \in sl by smt(is_path_mem).
     have wf_ptr_min: wf_ptr sl minf. by smt().
     have wf_ptr_l1: forall p, p \in l1 => wf_ptr sl p. by smt(is_path_wf_ptr).
     have wf_ptr_l2: forall p, p \in l2 => wf_ptr sl p. by smt(is_path_wf_ptr mem_cat is_path_path).
     have node_pinf : sl3.[pinf] = {| key = Pinf; data = witness; forward = mkarray []; |}.
     + by smt(Array_size_eq0 setE wf_pinf_in).
     have key_pinf : Key sl3 pinf = Pinf.
     + by rewrite node_pinf.
     have height_pinf : height sl3 pinf = 0.
     + by rewrite node_pinf Array_size_eq0.


     have ip3 : is_path sl3 minf (l1 ++ fresh_ptr sl :: l2) pinf.
     + apply (is_path_trans stk.[0]).
       + by apply : is_path_imp (hpl1); smt(setE).
       rewrite /= !andbA. split; 1:smt(is_path_mem).
       move: {heqpath fresh_ne_l2 minf_ne_l2 stkh_ne_l2}.
       case: l2 hpl2 wf_ptr_l2 mem_l2 => [/# | p2 l2 /= |> 2? hpl2 wf_ptr_l2 mem_l2 ].
       rewrite /= !andbA; split; 1: by smt().
       apply: is_path_imp (hpl2) => p hpin.
       smt(is_path_in is_path_lt EK.lt_nle).

     have path3 := is_path_path _ _ ip3.
     have path3_iff : forall p, p \in path sl3 <=> (p = fresh_ptr sl \/ p \in path sl).
     + smt(mem_cat).
     have ltp_eq : forall p q,
         ltp sl p q <=> (p <> fresh_ptr sl /\ q <> fresh_ptr sl /\ ltp sl3 p q).
     + by smt().
     have ltp_from_fresh: forall p h,
       0 <= h < size stk => ltp sl3 (fresh_ptr sl) p => ltp sl stk.[h] p.
     + by smt(EK.lt_trans EK.lt_nle mem_cat).

     suff : wf sl3.
     + move=> hwf3; rewrite hwf3 /=.
       have k_nin: forall (p : ptr), p \in minf :: path sl => Key sl p <> K k.
       + move=> p [ ->> /#| hin]; apply /negP => hpK.
         move: hin; rewrite heqpath mem_cat => -[ ] hin.
         + smt(is_path_bound EK.lt_nle).
         have := hlast 0 _;1: smt().
         case: (l2) hpl2 (is_path_lt _ _ _ _ hpl2) hin => />.
         smt(is_path_bound EK.lt_nle).
       split.
       + apply fmap_eqP => x.
         rewrite !SmtMap.get_setE.
         case: (x = K k) => [->> | hne].
         + rewrite -key_fresh dslE_in //=; 1:smt(mem_cat); rewrite // setE (:fresh_ptr sl <> minf) 1:/# setE //.
         rewrite !dslP //.
         case: (exists (p : ptr), (p \in minf :: path sl) /\ Key sl p = x); 2: smt(mem_cat).
         move=> [p [hin heq]]; rewrite -heq get_ptr_in //.
         have ? := is_path_mem _ p _ _ _ (pathP sl (wf_has_path sl hwf)) hin.
         have [hh1 hh2]: (p = minf \/ (p \in path sl3)) /\ Key sl3 p = Key sl p.
         + smt(mem_cat).
         have -> : exists (p0 : ptr), (p0 = minf \/ (p0 \in path sl3)) /\ Key sl3 p0 = Key sl p.
         + by exists p.
         rewrite -hh2 get_ptr_in //; smt(setE).
       have -> /= : ! K k \in hsl sl.
       + by rewrite domE /= hslP 1:// /#.
       apply fmap_eqP => x; rewrite !SmtMap.get_setE.
       case: (x = K k) => [->> | hne].
       + by rewrite -key_fresh hslE_in //; smt().
       case: (x = Minf) => [->> | hne1].
       + have [heq1 heq2]: sl.[minf].`key = Minf /\ sl3.[minf].`key = Minf by smt().
         rewrite -{1}heq2 -heq1 !hslE_in // /#.
       rewrite !hslP //.
       case: (exists (p : ptr), (p \in minf :: path sl) /\ Key sl p = x); 2: smt(setE).
       move=> [p [hin heq]]; rewrite -heq get_ptr_in //.
       have ? := is_path_mem _ p _ _ _ (pathP sl (wf_has_path sl hwf)) hin.
       have [hh1 hh2]: (p = minf \/ (p \in path sl3)) /\ Key sl3 p = Key sl p.
       + smt(setE).
       have -> : exists (p0 : ptr), (p0 = minf \/ (p0 \in path sl3)) /\ Key sl3 p0 = Key sl p.
       + by exists p.
       rewrite -hh2 get_ptr_in //; smt().

     have sl3_has_path : has_path sl3 minf pinf by exists (l1 ++ fresh_ptr sl :: l2).

     split; 1:by smt().
     rewrite andbA; split; 1: by smt(setE).
     have minf_in_sl3 : in_path sl3 minf by done.
     have fresh_in_sl3 : in_path sl3 (fresh_ptr sl) by smt().
     have stk_in_sl3 : forall h, 0 <= h < height sl minf => in_path sl3 stk.[h] by smt(mem_cat).

     exists (l1 ++ fresh_ptr sl :: l2); split => //.
     move=> p; rewrite -cat_cons mem_cat => -[].
     + move=> p_in; rewrite /wf_ptr height_minf.
       have p_nfresh : p <> fresh_ptr sl by smt(is_path_mem).
       (* have [wf_ht wf_ptr_at]:= is_path_wf_ptr _ _ _ hwf hpl1 _ p_in. *)
       split; 1: smt().
       move=> h hh /=.
       case: (p = minf /\ size stk <= h). move => [->> gg].
       + rewrite fwd_fresh2 1://. move: hh. rewrite height_minf. move => hh. smt().
         split; 1:smt().
         exists l1. move: ip3; rewrite -cat_rcons is_path_cat last_rcons. rewrite allP. by smt().
       move=> hh1.
       case: ((0 <= h < min (size fwk) (size stk)) /\ p = stk.[h]) =>  [ [hh2 ->>] | hp].
       + rewrite fwd_fresh1 1:/#. split; 1:smt().
         apply ltp_all => //.
         + by smt(EK.lt_trans).
         move=> p lt1 lt2 /=.
         by have :=wf_ptr_between sl stk.[h] h p hwf; smt(EK.lt_trans EK.lt_nle).

       have [hwfp1 /(_ h _) /=] := is_path_wf_ptr _ _ _ hwf hpl1 _ p_in; 1: smt().
       move=> [hei hex].
       have p_in_slp : in_path sl p by rewrite /in_path heqpath -cat_cons mem_cat p_in.
       have {hex} [/= hlt hall] := all_ltp sl p _ _ (wf_has_path sl hwf) (wf_pinf sl hwf) p_in_slp hex.
       have hpsl:= is_path_mem sl p minf l1 stk.[0] hpl1 p_in.
       have ->: (Forward sl3 p).[h] = (Forward sl p).[h]. smt().
       have ?: (Forward sl p).[h] <> minf. smt(EK.lt_nle).
       have ?: (Forward sl p).[h] <> fresh_ptr sl.
       + by have /#:= is_path_mem sl (Forward sl p).[h] minf (path sl) pinf (pathP sl (wf_has_path sl hwf)).
       + split; 1:smt().
         apply ltp_all => //=.
         + by smt().
         move=> q ??; have ? : q <> minf. smt(EK.lt_trans EK.lt_nle).
         case (q = fresh_ptr sl); smt().
     move => //= [->> | p_in_tail].
     + split; 1: smt().
       move => h; rewrite height_fresh; move => hh. split; 1:smt().
       apply ltp_all => //.
       + smt(pinf_in_path forward_in_path mem_cat).
       move => p * /=. rewrite height_retained; 1,2:smt(EK.lt_nle).
       case (h < size stk) => hh1.
       + apply (wf_ptr_between sl stk.[h] h p hwf); smt(forward_in).
       smt(pinf_in_path mem_cat).
     have := is_path_wf_ptr sl (path sl) pinf hwf (pathP sl (wf_has_path sl hwf)) p _; 1: smt(mem_cat).
     have ? := is_path_mem _ p _ _ _ hpl2 _; 1: by rewrite /= p_in_tail.
     have hne : p <> fresh_ptr sl by smt().
     have hne1 : minf <> fresh_ptr sl by smt(wf_minf_in).
     move=> [hh1 hh2]; split; 1:smt().
     move=>h ; rewrite height_retained 1,2:/#; move=> hh.
     have ? := forward_in sl (path sl) pinf hwf (pathP sl (wf_has_path sl hwf)) p _ h _; 1,2: smt(mem_cat).
     have hKp : K k < Key sl p.
     + case: (l2) hpl2 p_in_tail => /> l2' ???? hpl2 [->> // | p_in_tail].
       have [l21 l22 []]:= is_path_in sl _ _ _ p hpl2 _; 1: by rewrite /= p_in_tail.
       by move=> /is_path_lt; smt(EK.lt_trans).
     have /= [? hex]:= hh2 _ hh.
     have [hlt hall]:= all_ltp _ _ _ _ (wf_has_path sl hwf) (wf_pinf sl hwf) _ hex.
     + smt(mem_cat).
     have ->: (Forward sl3 p).[h] = (Forward sl p).[h] by smt().
     split; 1: smt().
     apply ltp_all => //; smt(mem_cat EK.lt_nle).
  qed.

  phoare insert_h_spec_ll sl_ k_ d_ hk_:
   [ SL.insert_h :
     wf sl /\ (sl,k,d,hk) = (sl_, k_, d_, hk_) /\ 0 <= hk
     ==>
     wf res /\ dsl res = (dsl sl_).[K k_ <- d_] /\
     hsl res =
       let hsl_ = hsl sl_ in
       if K k_ \in hsl_ then hsl_
       else hsl_.[Minf <- max hsl_.[Minf] (hk_ + 1)].[K k_ <- hk_ + 1]
   ] = 1%r.
  proof.
    conseq (:  wf sl ==> true) ( insert_h_spec sl_ k_ d_ hk_) => //.
    proc. seq 5: true; 1,4,5: by auto.
    + while ( wf sl /\ 
              -1 <= h < height sl pos /\ pos <> pinf /\
              nexts = (sl.[pos]).`forward /\
              exists l1 l2, is_path sl minf l1 pos /\ is_path sl pos l2 pinf) 
            (* Variant *)
            (size (path_btw sl pos pinf) + h).
      + move=> z; auto => |> &hr; move: (sl{hr}) (h{hr}) (pos{hr}) (k{hr}) => sl h pos k.
        move=> hwf _ hhei hpinf l1 l2 hpl1 hpl2 h0h.
        have h0hei : 0 <= h < height sl pos by done.       
        have [? /(_ h h0hei) |> hheif l21 hp21 hall] := wf_ptr_last _ _ _ hwf hpl1.
        have |> l22 hp22 heq2 := is_path_pinf _ _ _ _ _ hwf hp21 hpl2.
        split; 1: smt().
        move=> hK; rewrite andbA; split.
        + split; 1: smt().
          exists (l1 ++ rcons l21 (sl.[pos]).`forward.[h]) l22; split => //.
          by apply: is_path_trans hpl1 hp21.
        rewrite (is_path_path_bth _ _ _ _ hpl2) (is_path_path_bth _ _ _ _ hp22) heq2 size_cat.
        smt(List.size_ge0).
      auto => |> &hr; move: (sl{hr}) => sl {&hr} hwf.
      split. 
      + rewrite !andbA; split; 1: smt (size_ge0).
        exists [] (path sl). rewrite /=. smt(wf_has_path pathP).
      move=> h pos _ _ hpinf _ l2 _ hpl2.
      rewrite ( is_path_path_bth _ _ _ _ hpl2).
      have := is_path_lt _ _ _ _ hpl2.
      smt(List.size_ge0).
    if; auto; while (true) (size stk - h); auto; smt(size_ge0).
  qed.

  module ASL = { 

    proc insert (sl: hsl, k: key, d:data) = { 
      var hk, ek;
      ek <- K k;
      hk <$ hbino;
      if (ek \notin sl) { 
        hk <- hk + 1;
        sl.[Minf] <- max (sl.[Minf]) hk;
        sl.[ek] <- hk;
      }
      return sl;
    }

    proc build (l : (key * data) list) : hsl = { 
      var sl, k, d;
      sl <- SmtMap.empty;
      sl.[Minf] <- 1;
      sl.[Pinf] <- 0;

      while (l <> []) { 
        (k, d) <- head witness l;
        l <- behead l;
        sl <@ insert (sl, k, d);
      }
      return sl;
    }

    proc build_find (l : (key * data) list, k : key) : int = { 
      var sl;
      sl <@ build(l);
      return path_len sl (K k);
    } 

    proc path_length (l : (key * data) list, k : key) : int = { 
      var dom, h, sz, lv, c;
      dom <- rev (sort K.(<=) (undup (unzip1 l)));
      h <- 1;  
      c <- 0;
      lv <- -1;
      while (dom <> [] /\ k < head witness dom) {
        sz <$ hbino;
        sz <- sz + 1;
        h <- max sz h;
        dom <- behead dom;
      } 
      while (dom <> []) { 
        dom <- behead dom;
        sz <$ hbino;
        sz <- sz + 1;
        h <- max sz h;
        if (lv < sz) {
          c <- c + sz - lv;
          lv <- sz - 1;
        }
      }
      return c + (h - lv - 1);
    }

    proc path_length_single (l : (key * data) list, k : key) : int = {
      var dom, h, sz, lv, c;
      dom <- rev (sort K.(<=) (undup (unzip1 l)));
      h <- 1;
      c <- 0;
      lv <- -1;
      while (dom <> []) {
        sz <$ hbino;
        sz <- sz + 1;
        h <- max sz h;
        dom <- behead dom;
        if (lv < sz /\  head witness dom <= k) {
          c <- c + sz - lv;
          lv <- sz - 1;
        }
      }
      return c + (h - lv - 1);
    }
  }.

  equiv e_insert : SL.insert ~ ASL.insert : 
    wf sl{1} /\ hsl sl{1} = sl{2} /\ ={k,d}
    ==> 
    wf res{1} /\ hsl res{1} = res{2}. 
  proof. proc; ecall{1} (insert_h_spec_ll sl{1} k{1} d{1} hk{1}); auto => /> />. smt(hbino_supp).
qed.

  equiv e_build : SL.build ~ ASL.build : 
    ={l} 
    ==> 
    wf res{1} /\ hsl res{1} = res{2}. 
  proof. 
    proc.
    while (={l} /\ hsl sl{1} = sl{2} /\ wf sl{1}); 1: by call e_insert; auto.
    auto => |>; rewrite wf_empty /= /hsl /bindings path_empty /= empty_minf empty_pinf /=.
    rewrite !size_mkarray /=; apply fmap_eqP => k.
    rewrite ofassoc_get !assoc_cons assoc_nil !get_setE emptyE /#.
  qed.

  equiv e_build_find : SL.build_find ~ ASL.build_find : ={arg} ==> ={res}.
  proof. proc; ecall{1} (find_spec_ll sl{1} k{1}); call e_build; auto. qed.

  section.

  local clone import PROM.FullRO as PRO with 
    type in_t <- key,
    type out_t <- int,
    op dout <- fun _ => hbino,
    type d_in_t <- (key * data) list * key,
    type d_out_t <- int
  proof *. 
  
  local module ASL_RO (O:RO) = { 
    proc path_length(dom: key list, k:key) = {
      var h, c, lv, k', sz;  
      h <- 1;  
      c <- 0;
      lv <- -1;
      while (dom <> [] /\ k < head witness dom) {
        k' <- head witness dom;
        sz <@ O.get(k'); 
        sz <- sz + 1;
        h <- max sz h;
        dom <- behead dom;
      } 
      while (dom <> []) { 
        k' <- head witness dom;
        dom <- behead dom;
        sz <@ O.get(k');
        sz <- sz + 1;
        h <- max sz h;
        if (lv < sz) {
          c <- c + sz - lv;
          lv <- sz - 1;
        }
      }
      return c + (h - lv - 1);
    }

    proc build (l : (key * data) list) = {
      var sl, dom, dom_, hk, k, d, ek; 
      dom_ <- rev (sort K.(<=) (undup (unzip1 l)));
      (* Init the random oracle *)
      O.init();
      dom <- dom_;
      while (dom <> []) { 
        k <- head witness dom;
        dom <- behead dom;
        O.sample(k);
      }

      (* Init hsl *)
      sl <- SmtMap.empty;
      sl.[Minf] <- 1;
      sl.[Pinf] <- 0;
      while (l <> []) { 
        (k, d) <- head witness l;
        l <- behead l;
        ek <- K k;
        if (ek \notin sl) { 
          hk <@ O.get(k);
          hk <- hk + 1;
          sl.[Minf] <- max sl.[Minf] hk;
          sl.[ek] <- hk;
        }
      }
      return dom_;
    }

    proc distinguish (l : (key * data) list, k:key) : int = {
      var dom, c;
      dom <@ build(l);
      c <@ path_length(dom, k);
      return c;
    }

  }.

lemma set_not_empty (m:('a,'b)fmap) a b : m.[a <- b] <> SmtMap.empty.
proof. by apply /negP => heq; have := SmtMap.get_setE m a a b; rewrite heq emptyE. qed.

  local equiv ASL_ASL_LRO_build : ASL.build ~ ASL_RO(LRO).build : ={arg} ==> 
    (forall k, SmtMap."_.[_]" res{1} (K k) = omap (fun x => x + 1) RO.m{2}.[k]) /\
    (forall k, k \in res => k \in RO.m){2} /\ 
    res{1}.[Minf] = listmax_bounded Int.(<=) 1 (map (fun k => oget RO.m{2}.[k] + 1) res{2}) /\ 
    elems res{1} = Pinf :: map K res{2} ++ [Minf].
  proof.
    proc; inline *.
    exlim l{1} => l_.
    while(={l,sl} /\
          (if RO.m{2} = SmtMap.empty then sl{1}.[Minf] = 1
            else exists k, k \in RO.m{2} /\ oget RO.m{2}.[k] + 1 = sl{1}.[Minf]) /\
          (forall k, k \in RO.m{2} => 1 <= oget RO.m{2}.[k] + 1 <= sl{1}.[Minf]) /\
          (forall k, SmtMap."_.[_]" sl{1} (K k) = omap (fun x => x + 1) RO.m{2}.[k]) /\
          (forall k, k \in unzip1 l_ <=> (k \in RO.m \/ k \in unzip1 l)){2} /\
          (forall k, (k \in sl{1} \/ k \in map K (unzip1 l{1})) <=> (k = Pinf \/ k = Minf \/ k \in map K dom_{2}))).
    + inline{1} ASL.insert.
      sp 6 3; wp; inline *; if{2}; auto => |> &1 &2 [// | [k1 d1] l1] |>;
        smt(SmtMap.get_setE SmtMap.mem_set set_not_empty hbino_supp).
    wp; while{2} true (List.size dom{2}).
    + by auto => |> &hr hdom; rewrite -{2}(head_behead _ witness hdom) /= /#.
    auto => |> dom.
    have hK : injective K by move=> ?/>.
    split; 1: smt(size_eq0 size_ge0).
    split. 
    + split; 1: by rewrite !get_setE.
      split; 1: by move=> ?; rewrite mem_empty.
      split; 1: by move=> ?; rewrite !get_setE !emptyE.
      split; 1: by move=> ?; rewrite mem_empty.
      move=> k1; rewrite !SmtMap.mem_set map_rev SmtMap.mem_empty /= mem_rev.
      by case: k1 => // k1 /=; rewrite !(mem_map K hK) mem_sort mem_undup.
    move=> m sl hinf hmax hget hdom hsl; split; 2: split.
    + by move=> k1; rewrite mem_rev mem_sort mem_undup hdom.
    + pose li := List.map _ _. 
      have -> : listmax_bounded Int.(<=) 1 li = listmax Int.(<=) 1 (1 :: li) by done.
      have -> : listmax Int.(<=) 1 (1 :: li) = listmax Int.(<=) 1 li.
      + have : forall z, z \in li => 1 <= z. 
        + by move=> z /mapP /> k; rewrite mem_rev mem_sort mem_undup hdom => /hmax |>.
        by case: li => //= ?? ->.
      rewrite /li; case: (rev _) hsl => {li} [ | k lk] hsl.
      + move: hinf; have -> // : m = SmtMap.empty.
        by apply fmap_eqP => k; rewrite emptyE; case _ : m.[k] => // /#.
      move: hinf; have -> : m <> SmtMap.empty.      
      + by apply/negP => heq; have /# : m.[k] = None by rewrite heq emptyE.
      have : (k::lk) <> [] by done.
      move: (k::lk) hsl => {k lk} lk hsl hnil.
      pose li := List.map _ _. 
      move=> /> k hk heq.
      have := listmax_in Int.(<=) lez_trans lez_total 1 li _.
      + by smt(size_eq0 size_ge0). 
      move=> /mapP [k1 /= [hin heq']].
      have := listmax_gt_in Int.(<=) lez_trans lez_total 1 li sl.[Minf] _.
      + by apply /mapP; exists k => /=; smt(List.mapP).
      have := hmax k1 _; 1: smt(List.mapP).
      by rewrite heq' => {hmax hget hsl heq heq' hK li hin hk hnil} /#.
    move=> {hinf hmax}.    
    have -> : Pinf :: (map K (rev (sort K.(<=) (undup (unzip1 l_)))) ++ [Minf]) = 
              rev (Minf :: map K (sort K.(<=) (undup (unzip1 l_))) ++ [Pinf]).
    + by rewrite rev_cat rev_cons rev_nil rev_cons /= -cats1 map_rev.
    rewrite /elems; congr.
    apply: (eq_sorted EK.(<=)).
    + by apply EK.le_trans. + smt (EK.lt_nle). + by apply/sort_sorted/EK.le_total.
    + rewrite -cat1s; apply sorted_cat => //; 1: by apply EK.le_trans.
      + apply sorted_cat => //; 1: by apply EK.le_trans.
        + by apply (sorted_map K.(<=)) => //; apply/sort_sorted/K.le_total.
        by move=> _ _ /= -> /mapP />.
      by move=> /=; smt(mapP).
    apply uniq_perm_eq.
    + by apply/sort_uniq/uniq_elems.
    + rewrite /= cat_uniq map_inj_in_uniq; 1: by move=> 4?; apply hK.
      rewrite sort_uniq undup_uniq mem_cat /=; smt(mapP).
    by move=> k; rewrite mem_sort -memE mem_fdom mem_cat /= hsl map_rev mem_rev; case: k. 
  qed.

  local hoare h_ASL_RO_path_length sl k_ : ASL_RO(LRO).path_length : 
    (forall k, SmtMap."_.[_]" sl (K k) = omap (fun x => x + 1) RO.m.[k]) /\
    (forall k, k \in dom => k \in RO.m) /\ 
    sl.[Minf] = listmax_bounded Int.(<=) 1 (map (fun k => oget RO.m.[k] + 1) dom) /\
    elems sl = Pinf :: map K dom ++ [Minf] /\ k = k_ ==> 
    res = path_len sl (K k_).
  proof.
    proc.
    while ( sl.[Minf] = listmax_bounded Int.(<=) h (map (fun k0 => oget RO.m.[k0] + 1) dom) /\ lv < h /\
            (forall k, SmtMap."_.[_]" sl (K k) = omap (fun x => x + 1) RO.m.[k]) /\
            (forall k, k \in dom => k \in RO.m) /\ 
            walk_back sl (0, -1) (predecessors sl (K k)) = walk_back sl (c,lv) (rcons (map K dom) Minf) ).
    + inline LRO.get.
      rcondf 5; 1: by auto => /> /#.
      auto => /> &hr; case: (dom{hr}) => // k1 dom1 /> -> hlt hget hin -> _ _.
      rewrite /max (ltzNge _ h{hr}) if_neg /=. 
      rewrite walk_back_cons /walk_back_step /= hget /=. 
      move: (hin k1); rewrite domE /= ltzNge. 
      by case: (RO.m{hr}.[k1]) => //= hk1 /> /#. 
    exlim dom => dom_.      
    while ( sl.[Minf] = listmax_bounded Int.(<=) h (map (fun k0 => oget RO.m.[k0] + 1) dom) /\ lv < h /\
            (forall k, SmtMap."_.[_]" sl (K k) = omap (fun x => x + 1) RO.m.[k]) /\
            (forall k, k \in dom => k \in RO.m) /\ 
            exists l, dom_ = l ++ dom /\ forall k', k' \in l => k < k').
    + inline LRO.get.
      rcondf 4; 1: by auto => /> /#.
      auto => /> &hr; case: (dom{hr}) => // k1 dom1 /> -> hlvh hget hin l halllt hlt _ _.
      rewrite /max (ltzNge _ h{hr}) if_neg /=; rewrite andbA; split; 1: smt().
      exists (rcons l k1); rewrite cat_rcons /= => k2; rewrite mem_rcons /= => -[ /> | ].
      by apply halllt.
    auto => /> &hr hget hin hMinf helems; split; 1: by exists [].
    move=> m dom0 h0 hdom0 4? l ->> hl; split; last first.
    + move=> _ c lv hlt _; rewrite /path_len => ->.
      by rewrite /walk_back /= /walk_back_step /= lezNgt hlt /b2i /=; ring.
    rewrite /predecessors /= helems map_cat -catA -cat_cons cats1 find_cat.
    have -> : ! has (fun (k'0 : ekey) => k'0 <= K k_) (Pinf :: map K l).
    + by apply/negP => /hasP [_] [] /= [-> //| /mapP />] k /hl; rewrite -EK.lt_nle.
    have -> : find (fun (k'0 : ekey) => k'0 <= K k_) (rcons (map K dom0) Minf) = 0.
    + by case: (dom0) hdom0 => //=; smt(K.lt_nle).
    by pose hd := Pinf :: _; rewrite /= drop_size_cat.
  qed.

  local phoare h_ASL_RO_path_length_ll sl k_ :  [
    ASL_RO(LRO).path_length : 
      (forall k, SmtMap."_.[_]" sl (K k) = omap (fun x => x + 1) RO.m.[k]) /\
      (forall k, k \in dom => k \in RO.m) /\ 
      sl.[Minf] = listmax_bounded Int.(<=) 1 (map (fun k => oget RO.m.[k] + 1) dom) /\
      elems sl = Pinf :: map K dom ++ [Minf] /\ k = k_ 
      ==> 
      res = path_len sl (K k_) 
    ] = 1%r.
  proof.
    conseq (: true  ==> true) ( h_ASL_RO_path_length sl k_) => //.
    proc.
    while(true) (size dom). 
    + by move=> z; auto; call (: true); [ islossless | auto => /#].
    while(true) (size dom). 
    + by move=> z; auto; call (: true); [ islossless | auto => /#].
    auto; smt(size_eq0 size_ge0).
  qed.
 
  local equiv ASL_ASL_LRO : ASL.build_find ~ ASL_RO(LRO).distinguish : ={arg} ==> ={res}.
  proof.
    proc; ecall{2} (h_ASL_RO_path_length_ll sl{1} k{2}); call ASL_ASL_LRO_build; auto.
  qed.

  local equiv ASL_LRO_RO : ASL_RO(LRO).distinguish ~ ASL_RO(RO).distinguish : ={arg, RO.m} ==> ={res}.
  proof. symmetry; conseq (FullEager.RO_LRO_D ASL_RO _) => // ?; apply hbino_ll. qed.

  local module ASL_RO' (O:RO) = { 

    proc build (l : (key * data) list) = {
      var dom, dom_, k; 
      dom_ <- rev (sort K.(<=) (undup (unzip1 l)));
      (* Init the random oracle *)
      O.init();
      dom <- dom_;
      while (dom <> []) { 
        k <- head witness dom;
        dom <- behead dom;
        O.sample(k);
      }

      return dom_;
    }

    proc distinguish (l : (key * data) list, k:key) : int = {
      var dom, c;
      dom <@ build(l);
      c <@ ASL_RO(O).path_length(dom, k);
      return c;
    }

  }.
 
  local equiv ASL_RO_RO' : ASL_RO(RO).distinguish ~ ASL_RO'(RO).distinguish : ={arg} ==> ={res}.
  proof.
    proc; sim 1 1.
    call (: ={arg} ==> ={res, RO.m}); 2: by auto.
    proc.
    while{1} (RO.m{1} = RO.m{2} /\ forall k d, (k,d) \in l{1} => k \in RO.m{1}) (size l{1}).
    + move=> &2 z; sp; if; inline *.
      + by rcondf ^if; auto => |>; smt(hbino_ll).
      by auto => |> /#. 
    wp.
    while (={RO.m, dom} /\ (forall k, k \in dom_ => (k \in RO.m \/ k \in dom)){2}).
    + inline *; auto => />; smt(SmtMap.get_setE).
    inline *; auto => /> &2 m h; split; 2: smt(size_eq0 size_ge0).
    move=> k d hk;apply h.
    by rewrite mem_rev mem_sort mem_undup mem_map_fst; exists d.
  qed.

  local equiv ASL_RO'_LRO : ASL_RO'(RO).distinguish ~ ASL_RO'(LRO).distinguish : ={arg, RO.m} ==> ={res}.
  proof. conseq (FullEager.RO_LRO_D ASL_RO' _) => // ?; apply hbino_ll. qed.

  local equiv ASL_RO'_ASL_path_length : ASL_RO'(LRO).distinguish ~ ASL.path_length : ={arg} ==> ={res}.
  proof.
    proc; inline *; wp.
    while(={h, lv} /\ c0{1} = c{2} /\ dom1{1} = dom{2} /\ (uniq dom1 /\ forall k1, k1 \in dom1 => k1 \notin RO.m){1}).
    + by auto => /> &1 &2; case: (dom{2}) => />; smt(SmtMap.get_setE).
    while(={h} /\ (k1,dom1){1} = (k,dom){2} /\ (uniq dom1 /\ forall k1, k1 \in dom1 => k1 \notin RO.m){1}).
    + by auto => /> &1 &2; case: (dom{2}) => />; smt(SmtMap.get_setE).
    auto; while{1} true (size dom0{1});1: by auto; smt(size_ge0).
    auto => /> &2 dom.
    rewrite rev_uniq sort_uniq undup_uniq; smt (SmtMap.emptyE size_eq0 size_ge0).   
  qed.

  equiv build_sort_path_len : ASL.build_find ~ ASL.path_length : ={arg} ==> ={res}.
  proof.
    transitivity ASL_RO(LRO).distinguish (={arg} ==> ={res}) (={arg} ==> ={res}) => //; 1:smt().
    + by apply ASL_ASL_LRO.
    transitivity ASL_RO(RO).distinguish  (={arg,RO.m} ==> ={res}) (={arg} ==> ={res}) => //; 1:smt().
    + by apply ASL_LRO_RO.
    transitivity ASL_RO'(RO).distinguish (={arg} ==> ={res}) (={arg} ==> ={res}) => //; 1:smt().
    + by apply ASL_RO_RO'.
    transitivity ASL_RO'(LRO).distinguish (={arg,RO.m} ==> ={res}) (={arg} ==> ={res}) => //; 1:smt().
    + by apply ASL_RO'_LRO.
    apply  ASL_RO'_ASL_path_length .
  qed.

  end section.

  (* ********************************************************************** *)
  (*                                                                        *)
  (* final analysis of ASL.path_length                                      *)
  (*                                                                        *)
  (* ********************************************************************** *)

  abbrev log2 (n:int) = log2 n%r.

  (* to solve the final recurrence we need two observations coming from analysis*)
  (* for brevity, we axiomatise these  *)
  axiom f1 (D:real) : 0%r <= D < 1%r => D / 2%r ^ D + 2%r / 3%r / 2%r ^ (2%r * D) <= 1%r.
  axiom log2_split (n:int) : 1 <= n => 1%r/n%r + log2(n) <= log2(n+1).

  (* We introduce [inve i] := 1/2^i and prove some basic properties to make *)
  (* our life slightly easier *)
  (* ********************************************************************** *)
  op inve (i:int) = inv (2%r^i).

  lemma inve_ge0 (h:int) : 0%r <= inve h.
  proof. smt(expr_ge0 invr_ge0). qed.

  lemma inve_gt0 (h:int) : 0%r < inve h.
  proof. smt(expr_gt0 invr_gt0). qed.

  lemma inve_le1 (h:int) : 0 <= h => inve h <= 1%r.
  proof. smt(invr_le1 exprn_ege1). qed.

  lemma inve_lt1 (h:int) : 1 <= h => inve h < 1%r.
  proof. smt(invr_lt1 expr_gt0 exprn_egt1). qed.

  lemma inve_decr (h1 h2 : int) : h1 <= h2 => inve h2 <= inve h1.
  proof. smt(lef_pinv expr_gt0 rpow_int rpow_monoE). qed.

  lemma inve0 : inve 0 = 1%r.
  proof. by smt(RField.expr0). qed.

  lemma inve1 : inve 1 = inv 2%r.
  proof. by smt(RField.expr1). qed.

  lemma inveD (h k : int): inve h * inve k = inve (h+k).
  proof. rewrite /inve /= RField.exprD 1:/#. auto. qed.

  lemma inveS (k : int): inve (k + 1) = inve k / 2%r.
  proof. smt(inveD RField.expr1). qed.

  lemma inveN (h:int) : inve (-h) = inv (inve h).
  proof. by rewrite /inve  RField.exprN. qed.


  (* closed forms for finite series *)
  (* ********************************************************************** *)

  lemma finsum_geo_closed (p : real) (u : int): 0%r < p < 1%r => 0 <= u =>
    BRA.bigi predT (fun (x : int) => p^x) 0 u = (p^u - 1%r) / (p - 1%r).
  proof.
    move=> pne0.
    move: u; elim/intind; 1:smt(BRA.big_geq RField.expr0).
    move => i ii ih.
    rewrite BRA.big_int_recr 1:/# ih /= RField.exprD 1:/# RField.expr1 1:/#.
  qed.

  lemma finsum_geo1_closed u: 0 <= u =>
    BRA.bigi predT (fun (x : int) => 1%r/2%r^(x + 1)) 0 u = 1%r - 1%r/2%r^u.
  proof.
    move => uu.
    rewrite (BRA.eq_big_int 0 u _ (fun (x : int) => 1%r/2%r * (1%r/2%r)^x)); 1: smt(RField.exprD RField.expr1 RField.invfM RField.exprVn).
    rewrite -BRA.mulr_sumr finsum_geo_closed 1,2:/# /=. smt(RField.exprVn).
  qed.

  lemma finsum_geo_invex_closed u : 0 <= u =>
    BRA.bigi predT (fun (x:int) => 1%r/2%r^x * 1%r/2%r^(x + 1)) 0 u = (2%r/3%r) * (1%r - inv (2%r ^ (2*u))).
  proof.
    move => uu.
    rewrite (BRA.eq_big_int 0 u _ (fun (x : int) => 1%r/2%r * (1%r/4%r)^x)).
    + move=> i ii /=. rewrite RField.exprD 1:/# RField.expr1 RField.mulrA RField.invfM -RField.exprD 1:/#.
      have ->: i + i = 2 * i by smt().
      rewrite RField.exprM RField.expr2 /= RField.invfM RField.exprVn 1:/# //.
    rewrite -BRA.mulr_sumr finsum_geo_closed 1,2:/# /=.
    rewrite RField.exprM  RField.expr2 /= RField.exprVn 1:/# RField.invrM 1,2:/#.
    have ->: (inv (4%r ^ u) - 1%r) * (inv (inv 2%r) / (-3)%r) = - (inv (4%r ^ u) - 1%r) * 2%r / 3%r. smt().
    ring.
  qed.

  lemma finsum_geox_closed : forall u, 0 <= u =>
    BRA.bigi predT (fun (x:int) => x%r/2%r^(x + 1)) 0 u = 1%r - ((u%r+1%r)/2%r^u).
  proof.
    elim/intind; 1:smt(BRA.big_geq RField.expr0).
    move => k kge0 ih.
    rewrite BRA.big_int_recr 1:/# ih /= RField.exprD 1:/# RField.expr1 /=. ring.
    have -> /=: 2%r / (2%r ^ k * 2%r) = 2%r / 2%r * inv (2%r ^ k). ring; smt().
    smt().
  qed.

  
  (* the following collects some useful lemmas about [Ep hbino] *)
  (* ********************************************************************** *)

  lemma Ep_hbino_shift1 (f : int -> xreal):
     Ep hbino f = (inve 1)%xr * f 0 + (inve 1)%xr * Ep hbino (fun x => f (x + 1)).
  proof.
    rewrite -EpZ /=; 1:smt(of_realK inve1).
    rewrite (EpD1 _ _ 0) hbino1E /=; congr; 1:smt(rpow1 inve1 of_realK).
    have bijs : bijective (fun x => x + 1). exists (fun x => x - 1). by smt().
    rewrite (Ep_reindex (fun x => x + 1)) 1://.
    rewrite /Ep.
    have ->: (fun (x : int) =>
                mu1 (hbino \o fun (x0 : int) => x0 + 1) x **
                (\o) (fun (x0 : int) => if x0 <> 0 then f x0 else 0%xr)
                (fun (x0 : int) => x0 + 1) x)
             = (fun (x : int) => mu1 hbino x ** ((inve 1)%xr * f (x + 1))).
    + apply fun_ext. rewrite /(==). move => x. rewrite /(\o). rewrite muK. apply isdistr_inj; smt(bij_inj).
      case (x + 1 = 0)=> * /=. smt(hbino_supp supportP).
      case (0 <= x) => *; last first; 1: smt(hbino_supp supportP).
      rewrite /( ** ).
      rewrite !ifF; 1,2:smt(hbino_supp supportP of_realK).
      have -> /=: mu1 hbino (x + 1) = mu1 hbino x * inve 1.
      + rewrite !hbino1E. case (0 <= x) => *; rewrite !rpow_int 1,2://; smt(inveD).
      rewrite mulmA; congr. simplify. rewrite of_realM; 1,2:smt(supportP hbino_supp inve_ge0). done.
    done.
  qed.

  lemma Ep_hbino_shift (f : int -> xreal) (n:int) : 0 <= n =>
     Ep hbino f =
       BXA.bigi predT (fun x => (inve (x+1))%xr * f x) 0 n
       + (inve n)%xr * Ep hbino (fun x => f (x + n)).
  proof.
    elim: n. rewrite BXA.big_geq 1://  inve0 /=. done.
    move => n nn IH.
    have ->: (fun (x : int) => f (x + (n + 1))) = (fun (x : int) => f ((x + n) + 1)) by smt().
    pose fn:= fun x => f (x + n).
    have ->: (fun (x : int) => f (x + n + 1)) = (fun x => fn (x + 1)). by smt().
    rewrite IH.
    rewrite BXA.big_int_recr 1://.
    rewrite -addmA /=; congr.
    have ->: (inve (n + 1))%xr = (inve n)%xr * (inve 1)%xr.
    rewrite inveS; rewrite of_realM /=; 1,2:smt(inve_ge0); rewrite inve1. smt().
    rewrite -!mulmA -mulmDr.
    have ->: f n = fn 0. smt().
    rewrite Ep_hbino_shift1.
    done.
  qed.

lemma foo x :
  0 <= x => 1%r + (x%r + x%r^2)/2%r <= 2%r^x.
proof.
  elim: x => /=.
  + by rewrite RField.expr0z RField.expr0.
  move=> i h0i hrec; rewrite fromintD.
  have -> : 1%r + (i%r + 1%r + (i%r + 1%r) ^ 2) / 2%r = 
            1%r + (i%r + i%r^2)/2%r + (1%r + i%r) by field.
  rewrite RField.exprS 1://.
  have -> : 2%r * 2%r ^ i = 2%r ^ i + 2%r ^ i by ring.
  apply ler_add => //.
  apply: ler_trans hrec.
  have -> /# :  1%r + (i%r + i%r ^ 2) / 2%r = (1%r + i%r) + (i%r*(i%r - 1%r)/2%r) by field.
qed.

lemma bar (x : int) :
  0 <= x => x%r <= 2%r ^ (2 * x).
proof.
  elim x => /=.
  + by rewrite RField.expr0.
  move=> i h0i hrec; rewrite fromintD.
  case (i = 0) => [-> /= | ?]; 1: by smt(exprn_ege1).
  apply (ler_trans (i%r * 2%r ^ 2)).
  + rewrite RField.expr_pred 1:/# /= RField.expr1. smt(). (* AAAAAAAAAAAARRRRRRRRRRR *)
  have ->: 2 * (i + 1) = 2 * i + 2. by smt().
  rewrite RField.exprD 1:/#.
  apply ler_pmul; 1,2:smt(expr_ge0).
  apply hrec. done.
qed.

import RealSeq Discrete RealSeries.

lemma l1 (z x y : real) : z <> 0%r => x / y = (x * z) / (y * z).
proof.
move=> hz. case (y = 0%r) => [-> // | ].
by move=> ?; field => //; apply RField.unitrM.
qed.

  lemma Ep_hbino_id : Ep hbino (fun (x : int) => x%xr) = 1%xr.
  proof.
rewrite /Ep /=.
have -> /= : is_real (fun (x : int) => ((mu1 hbino x)%rp * x%rp)%xr) by move=> ?.
rewrite /psuminf.
have hD :
  Discrete.enumerate (fun (j : int) => Some j)
   (support (to_real (fun (x : int) => ((mu1 hbino x)%rp * x%rp)%xr))).
+ split; 1: smt().
  by rewrite /= /support /to_real /= => x hx; smt (hbino_supp).
have hsum: summable (to_real (fun (x : int) => ((mu1 hbino x)%rp * x%rp)%xr)).
+ rewrite (summable_from_bounded _ (fun j => Some j)) //.
  exists 1%r => n.
  rewrite (pmap_some (fun x => x)) map_id.
  rewrite (BRA.eq_big_int _ _ _ (fun (x:int) => x%r/2%r^(x + 1))) /=.
  + move=> i hi; rewrite /to_real ger0_norm 1:to_realP /= to_pos_pos 1:/#.
    rewrite RField.mulrC hbino1E.
    case (i = 0) => [-> // | ?].
    have -> //= : !(i < 0) by smt().
    by rewrite rpow_nat // 1:/#.
  case (0 <= n) => hn; last by rewrite BRA.big_geq 1:/#.
  rewrite (finsum_geox_closed n hn).
  have /# : 0%r <= (n%r + 1%r) / 2%r ^ n by apply divr_ge0; smt(expr_ge0).
rewrite hsum /= (sumE _ (fun j => Some j)) //=.
rewrite (lim_eq 1 _ (fun (u:int) =>  1%r - ((u%r+1%r)/2%r^u))).
+ move=> n hn /=; rewrite (pmap_some (fun x => x)) map_id.
  rewrite (BRA.eq_big_int _ _ _ (fun (x:int) => x%r/2%r^(x + 1))) /=.
  + move=> i hi; rewrite /to_real /= to_pos_pos 1:/#.
    rewrite RField.mulrC hbino1E.
    have -> //= : !(i < 0) by smt().
    by rewrite rpow_nat // 1:/#.
  by rewrite (finsum_geox_closed n) // 1:/#.
congr; apply lim_cnvto.
apply (squeeze_cnvto (fun u:int => 1%r - (1%r/u%r + 1%r/u%r^2)/(1%r/u%r^2 + (1%r/u%r + 1%r)/2%r)) 
             (fun u => 1%r) 1); last by apply cnvtoC.
+ move=> /= n hn. split.
  + apply ler_sub => //.
    have hn0 : n%r <> 0%r by smt().
    have -> : (inv n%r + inv (n%r ^ 2)) / (inv (n%r ^ 2) + (inv n%r + 1%r) / 2%r) =
              ((n%r + 1%r) / (1%r + (n%r + n%r^2)/2%r)).
    + by field => //; [ apply RField.unitrX | smt(expr_ge0)].
    apply ler_wpmul2l; 1: smt().
    apply lef_pinv; 1,2: smt(expr_gt0).
    by apply foo => /#.
  move => _.
  have /#: 0%r <= (n%r + 1%r) / 2%r ^ n by apply divr_ge0; smt(expr_ge0).
have {7}-> : 1%r =
             1%r - (0%r + 0%r) / (0%r + (0%r + 1%r) / 2%r) by done.
apply cnvtoB; 1: by apply cnvtoC.
apply cnvtoM.
+ by apply cnvtoD;[ apply cnvtoVn | apply cnvtoVn2].
apply cnvtoV_nz; 1: by apply RField.unitrV.
apply cnvtoD; 1: by apply cnvtoVn2.
apply cnvtoM; 2: by apply cnvtoC.
by apply cnvtoD; [ apply cnvtoVn | apply cnvtoC].
qed.

lemma Ep_hbino_exp : Ep hbino (fun (x : int) => (inve x)%xr) = (2%r/3%r)%xr.
proof.
rewrite /Ep /=.
have -> /= : is_real (fun (x : int) => ((mu1 hbino x)%rp * (inve x)%rp)%xr) by move=> ?.
rewrite /psuminf.
have hD :
  Discrete.enumerate (fun (j : int) => Some j)
   (support (to_real (fun (x : int) => ((mu1 hbino x)%rp * (inve x)%rp)%xr))).
+ split; 1: smt().
  by rewrite /= /support /to_real /= => x; rewrite hbino1E; move => hh; exists x; case (x < 0); smt(). (* SIMPLIFY? *)
have hsum: summable (to_real (fun (x : int) => ((mu1 hbino x)%rp * (inve x)%rp)%xr)).
+ rewrite (summable_from_bounded _ Some). apply hD.
  exists 1%r => n.
  rewrite (pmap_some (fun x => x)) map_id.
  rewrite (BRA.eq_big_int _ _ _ (fun (x:int) => 1%r/2%r^x * 1%r/2%r^(x + 1))) /=.
  + move=> i hi; rewrite /to_real /inve ger0_norm 1:to_realP /= to_pos_pos; 1:smt(expr_ge0).
    rewrite hbino1E.
    case (i = 0) => [-> /= | ?]; 1: by smt(rpow_nat).
    have -> /=: !(i < 0) by smt().
    by smt(rpow_nat).
  case (0 <= n) => hn; last by rewrite BRA.big_geq 1,2:/#.
  rewrite (finsum_geo_invex_closed n hn).
  have ? /#: 0%r <= inv (2%r ^ (2 * n)); by smt(invr_ge0 expr_ge0).
rewrite hsum /= (sumE _ (fun j => Some j)). apply hD. apply hsum. (* MA: //= gets stuck *)
rewrite (lim_eq 1 _ (fun (u:int) =>  2%r / 3%r * (1%r - inv (2%r ^ (2 * u))))) /=.
+ move=> n hn /=; rewrite (pmap_some (fun x => x)) map_id.
  rewrite (BRA.eq_big_int _ _ _ (fun (x : int) => 1%r / 2%r ^ x * 1%r / 2%r ^ (x + 1))).
  + move=> i hi; rewrite /to_real /= to_pos_pos; 1:smt(inve_ge0).
    rewrite hbino1E /inve.
    have -> /= : !(i < 0) by smt().
    by smt(rpow_nat).
  rewrite (finsum_geo_invex_closed n) 1,2:/#.
congr; apply lim_cnvto.
apply (squeeze_cnvto
        (fun u:int => 2%r/3%r * (1%r - 1%r/u%r))
        (fun u => 2%r/3%r) 1); last by apply cnvtoC.
+ move=> /= n hn; split.
  apply ler_wpmul2r; 1: smt().
  apply ler_wpmul2l; 1: smt().
  apply ler_sub; 1: smt().
  apply lef_pinv; 1,2: by smt(expr_gt0).
  apply bar; 1: smt().
+ move => ?.
  apply ler_wpmul2r; 1: smt().
  have {3}-> : 2%r = 2%r * (1%r - 0%r). by smt().
  apply ler_wpmul2l; 1: smt().
  apply ler_sub; 1: smt().
  apply invr_ge0. smt(expr_ge0).
have {2}-> : 2%r/3%r = 2%r / 3%r * (1%r - 0%r). by smt().
apply cnvtoM; 1: by apply cnvtoC.
apply cnvtoB; 1: by apply cnvtoC.
apply cnvtoVn.
qed.


  (* We use [f n m] to define the invariant for the two loops. the following collects *)
  (* some auxiliary lemmas*)
  (* ********************************************************************** *)

  op f (n m:int) = if m <= ceil (log2 (n + 1)) then ((log2 (n + 1) - m%r + 2%r)) else n%r * (inve (m-1)).


  lemma f_ge0 n m : 0 <= n => 0%r <= f n m.
  proof. smt(inve_ge0 ceil_bound). qed.

  lemma f_incr_1 (n1 n2 m : int) : 0 <= m => 0 <= n1 <= n2 => f n1 m <= f n2 m.
  proof.
  move => nn. rewrite /f.
    case (m <= ceil (log2 (n1 + 1))) => *. by smt(log_mono ceil_bound).
    case (m <= ceil (log2 (n2 + 1))) => *; last first. apply ler_pmul2r; 1,2:smt(inve_gt0).
    case (n1 = 0) => c0. rewrite c0 /=. (* MA: syntax? *) smt(ceil_bound).
    have ->: n1%r = 2%r ^ log2 n1 by smt(rpowK).
    have ->: 2%r ^ log2 n1 / 2%r ^ (m - 1) = 2%r ^ (log2 n1 - m%r + 1%r).
    + rewrite -rpow_int 1:/# -rpowN 1:/# -rpowD 1:/#. smt().
    apply (ler_trans (2%r^0%r)); last first; 1: smt(rpow_int RField.expr0 ceil_bound).
    apply rpow_monoE; smt(ceil_bound log_mono).
  qed.


  lemma rev_sorted ['a] (o: 'a -> 'a -> bool) l :
    (forall (y x z : 'a), o x y => o y z => o x z) => 
    sorted o l => 
    sorted (fun x1 x2 => o x2 x1) (rev l).
  proof.
    move=> htr; elim: l => //= a l hrec hpath.
    rewrite rev_cons -cats1.
    apply sorted_cat_cons => //=.
    + by apply/hrec; apply: path_sorted hpath.
    move=> y; rewrite mem_rev => hin.
    by have /allP := order_path_min o htr _ _ hpath; apply.
  qed.

  lemma Ep_hbino_f k n : 0 <= k => 0 <= n =>
    (2%r * inve k)%xr + Ep hbino (fun (x : int) => (f n (max (x + 1) k))%xr) <= (f (n + 1) k)%xr.
  proof.
    move => *.
    rewrite (Ep_hbino_shift _ k) 1:/# /=.
    rewrite (BXA.eq_big_int _ _ _ (fun x => (inve (x + 1))%xr * (f n k)%xr)) 1:/#.
    rewrite (eq_Ep _ _ (fun x => (f n (x + k + 1))%xr)); 1:smt(hbino_supp).
    rewrite BXA_mulDr bigiXR;1:smt(inve_ge0). rewrite finsum_geo1_closed 1:/#.

    rewrite /f /=.
    pose L := log2 (n + 1).
    case: (k <= ceil L) => c1.
    + have -> /=: k <= ceil (log2 (n + 2)) by smt(log_mono ceil_bound).
      rewrite (Ep_hbino_shift _ (ceil L - k)) 1:/#.
      rewrite /= (BXA.eq_big_int _ _ _ (fun x => (inve (x + 1) * (L - k%r + 1%r) - inve(x + 1) * x%r)%xr)).
      + move=> x xx /=. have -> /=: x + k + 1 <= ceil L by smt().
        rewrite -of_realM; 1,2:smt(inve_ge0 ceil_bound). smt().
      rewrite bigiXR /=. by move=> i hi; rewrite -RField.mulrBr; apply mulr_ge0; [apply inve_ge0 | smt(ceil_bound)].
      rewrite -BRA.sumrB -!BRA.mulr_suml finsum_geo1_closed 1:/# finsum_geox_closed 1:/#.
      rewrite (eq_Ep _ _ (fun x => (n%r * inve (ceil L)) ** (inve x)%xr)).
      + move=> x xx /=.
        have -> /=: !(x + (ceil L - k) + k + 1 <= ceil L). by smt(ceil_bound hbino_supp).
        have ->: inve (x + (ceil L - k) + k) = inve (ceil L) * inve x. by smt(inveD).
        rewrite -of_realM; 1,2: smt(inve_ge0 ceil_bound hbino_supp).
        done.
      rewrite EpsZ Ep_hbino_exp /=.
      rewrite !to_pos_pos; 1..4,6..9:smt(inve_ge0 inve_le1 ceil_bound log_mono).
      + rewrite subr_ge0 /inve.
        rewrite RField.mulrBl (RField.mulrC (Real.inv _)).
        case (ceil L = k) => [-> /= | ?];1: by rewrite RField.expr0.
        apply ler_sub => /=; 1: smt(ceil_bound).
        apply ler_pmul2r; 1:apply inve_gt0 => /#.
        by smt (ceil_bound).

      rewrite /inve !fromintB.
      have ->: (ceil L - k) = - (k - ceil L). ring.
      rewrite -!RField.exprN /= !RField.exprD 1:/# /=.
      have ->:
        2%r * 2%r ^ (-k) +
         ((1%r - 2%r ^ (-k)) * (L - k%r + 2%r) +
          2%r ^ (-k) *
          ((1%r - 2%r ^ k * 2%r ^ (- ceil L)) * (L - k%r + 1%r) -
           (1%r - ((ceil L)%r - k%r + 1%r) * (2%r ^ k * 2%r ^ (- ceil L))) +
           2%r ^ k * 2%r ^ (- ceil L) * (n%r * 2%r ^ (- ceil L) * 2%r) / 3%r))
        =
         L
         + 2%r ^ (-k) * 2%r ^ k * 2%r ^ (- ceil L) * ((ceil L)%r - L)
         + 2%r ^ (-k) * 2%r ^ k * 2%r ^ (- ceil L) * 2%r ^ (- ceil L) * 2%r/3%r * n%r
         - (k%r - 2%r).
        by ring.
      have ->: log2 (n + 2) - k%r + 2%r = log2 (n + 2) - (k%r - 2%r). by ring.
      apply ler_sub; 2: done.
      have -> /=: (2%r ^ -k) * 2%r ^ k = 1%r by rewrite -Num.Domain.exprD //; smt(rpow_int rpow0).
      pose D := (ceil L)%r - L.
      have ->: 2%r ^ - (ceil L) = inv (2%r^L * 2%r^D)
        by rewrite -rpowD // /D -rpowN // -rpow_int //; smt().
      rewrite rpowK 1,2,3:/#.
      rewrite RField.invrM; 1,2:smt(rpow_neq0).
      apply (ler_trans (L + inv (n+1)%r)); last smt(log2_split).
      rewrite -RField.addrA.
      rewrite ler_add 1:// -(RField.div1r (n + 1)%r) ler_pdivl_mulr 1:/#.
      have ? : 0%r < 2%r^D by apply rpow_gt0.
      rewrite RField.mulrDl.
      have ->: inv (2%r ^ D) * (1%r / (n + 1)%r) * D * (n + 1)%r
              = inv (2%r ^ D) * D * ((n + 1)%r / (n + 1)%r). by ring.
      have ->: inv (2%r ^ D) * (1%r / (n + 1)%r) * (inv (2%r ^ D) * (1%r / (n + 1)%r)) * 2%r * n%r / 3%r * (n + 1)%r
              = (inv (2%r ^ D) * inv (2%r ^ D)) * ((n + 1)%r / (n + 1)%r) * ((n%r / (n + 1)%r)) * 2%r/3%r. by ring.
      rewrite RField.divff 1:/#.
      apply (ler_trans (D/2%r^D + 2%r / 3%r * inv (2%r ^ (2%r * D)))).
      + rewrite RField.mulrC -RField.invfM.
        have -> /=: 2%r ^ D * 2%r ^ D = 2%r^(2%r * D) by smt(rpowD).
        apply ler_add; 1:smt().
        apply ler_pdivr_mulr. smt(rpow_gt0).
        have ->: 2%r / (3%r * 2%r ^ (2%r * D)) * (2%r ^ (2%r * D) * (n + 1)%r * 3%r)
                 = (n + 1)%r * 2%r * ((3%r * 2%r ^ (2%r * D))/ (3%r * 2%r ^ (2%r * D))).
        by ring.
        rewrite RField.divff; 1:smt(rpow_gt0).
        by smt().
      apply f1; 1:smt(ceil_bound).

     (* case ceil L < h *)
     rewrite (eq_Ep _ _ (fun x => ((n%r * inve k) ** (inve x)%xr))).
     + move => x /hbino_supp hx /=.
       have -> /=: !(x + k + 1 <= ceil L) by smt().
       rewrite -of_realM; 1,2:smt(inve_ge0). rewrite -inveD. done.
     rewrite EpsZ Ep_hbino_exp /=.
     rewrite !to_pos_pos; 1..6:smt(inve_le1 inve_ge0); 1:smt(ceil_bound inve_ge0).
     rewrite /inve -!RField.exprN /=.
     have ->: 2%r ^ - (k - 1) = 2%r * 2%r^(-k).
      + have ->: - (k - 1) = 1 - k by ring.
      by rewrite RField.exprD 1:/# RField.expr1.
     have ->: 2%r * 2%r ^ (-k) + ((1%r - 2%r ^ (-k)) * (n%r * (2%r * 2%r ^ (-k))) +
                                 2%r ^ (-k) * (n%r * 2%r ^ (-k) * 2%r) / 3%r)
             = (n + 1)%r * (2%r * 2%r ^ (-k))
               - 2%r * (1%r - 1%r/3%r) * n%r * (2%r ^ -k)  * (2%r ^ -k).
       by ring.
     apply ler_naddr; 1:smt(expr_ge0).
     case (k <= ceil (log2 (n + 2))) => c2 //.
     have ->: (n + 1)%r = 2%r ^ L. rewrite rpowK 1,2,3,4:/#.
     have ->: 2%r ^ L * (2%r * 2%r ^ -k) = 2%r ^ (1%r + L - k%r). 
     + by rewrite !rpowD // rpow1 // -fromintN -rpow_int //; ring.
     rewrite (ler_trans (2%r^0%r) _ _).
     + rewrite !rpowE 1,2:/#; apply exp_mono. apply ler_pmul2r; 1,2: smt(ln_gt0 ceil_bound).
     smt(ceil_bound rpow0).
   qed.


   ehoare path_length_cost_single : ASL.path_length_single :
      (2%r * log2 (size l + 1) + 4%r)%xr ==> res%xr.
   proof.
     proc.
     while ((0 <= c /\ 1 <= h /\ -1 <= lv < h)
            `|` (c%r + h%r - lv%r - 1%r + f (size dom) h  + f (size dom) (lv + 1) )%xr).
     + move=> &hr /=; apply xle_cxr_r => /> *. smt(f_ge0).
     + auto => &hr /=.
       move: (h{hr}) (lv{hr}) (c{hr}) (dom{hr}) (k{hr}) => {&hr} h lv c dom k.
       rewrite if_f_cxr /=.
       rewrite Ep_cxr /=; apply xle_cxr.
       move => *. split; 1:smt(hbino_supp).
       pose n := size (behead dom).
       have *: 0 <= n. by apply size_ge0.
       have ->: size dom = n+1. by smt().
       rewrite (eq_Ep _ _
                  (fun x =>
                    ((c%r - lv%r - 1%r + (max (x + 1) h)%r)%xr
                     + (f n (max (x + 1) h))%xr)
                    + (if lv < x + 1 /\ head witness (behead dom) <= k
                       then f n (x + 1) + 1%r
                       else f n (lv + 1))%xr)).
       + move => x * /=. case (lv < x + 1 /\ head witness (behead dom) <= k) => * /=; apply to_realK_eq => /=; smt(f_ge0).
       rewrite !EpD.
       rewrite (Ep_hbino_shift _ h) 1:/# /=.
       rewrite (BXA.eq_big_int _ _ _
                (fun x => (inve (x + 1))%xr * (c%r + h%r - lv%r - 1%r)%xr)) 1:/#.
       rewrite BXA_mulDr bigiXR; 1:smt(inve_ge0); rewrite finsum_geo1_closed 1:/#.
       rewrite (eq_Ep _ _ (fun (x : int) => x%xr + (c%r + h%r - lv%r)%xr)).
       + move => x /hbino_supp * /=.
         by rewrite -of_realD /#.
       rewrite EpD Ep_hbino_id EpC hbino_ll /=.
       (* HOW to do that properly *)
       have ->: ((1%r - inve h)%rp * (c%r + h%r - lv%r - 1%r)%rp
                + (inve h)%rp * (1%rp + (c%r + h%r - lv%r)%rp))%xr
               = (c%r + h%r - lv%r - 1%r)%xr + (2%r * inve h)%xr.
       + rewrite -of_realM; 1,2: smt(inve_le1). (*ARRR double proof non-negativity *)
         rewrite -of_realM /=; 1,2: smt(inve_ge0).
         have *: 0%r <= c%r + h%r - lv%r - 1%r. by smt().
         rewrite -of_realD /=; 1,2: smt(pmulr_rge0 inve_gt0 inve_lt1).
         rewrite -of_realD; 1,2:smt(inve_ge0).
         apply to_realK_eq => /=. rewrite !to_pos_pos; 1..4:smt(pmulr_rge0 inve_gt0 inve_lt1).
         ring.
       have -> : (c%r + h%r - lv%r - 1%r + f (n + 1) h + f (n + 1) (lv + 1))%xr
               = (c%r + h%r - lv%r - 1%r)%xr + (f (n + 1) h)%xr + (f (n + 1) (lv + 1))%xr.
               by do 2! (rewrite /= of_realD; 1,2:smt(f_ge0)).
       rewrite -!addmA; apply xler_add2l.
       rewrite addmA; apply xler_add.
       + apply Ep_hbino_f; 1,2:smt().
       case (head witness (behead dom) <= k) => /= *; last first.
       + by rewrite EpC hbino_ll /=; smt(f_incr_1 f_ge0).
       rewrite (eq_Ep _ _
                 (fun (x : int) => (lv < x + 1)%xr
                   + (f n (max (x + 1) (lv + 1)))%xr)); 1: smt(of_realD f_ge0).
       rewrite EpD.
       rewrite (Ep_hbino_shift _ (lv + 1)) 1:/# /=.
       rewrite (eq_Ep _ _ (fun _ => 1%xr)); 1:smt(hbino_supp).
       rewrite EpC hbino_ll /=.
       have ->: BXA.bigi predT (fun (x : int) => ((inve (x + 1))%rp * (b2r (lv < x + 1))%rp)%xr) 0 (lv + 1)
                = (0 <= lv)%xr * (inve (lv + 1))%xr.
       + case (0 <= lv) => * /=; last first. have -> /=: lv = -1 by smt(). by smt(BXA.big_geq).
         rewrite (BXA.big_cat_int lv) 1,2:/#.
         rewrite BXA.big_int1 /=. have -> /=: lv < lv + 1 by smt().
         rewrite (BXA.eq_big_int _ _ _ (fun (x : int) => 0%r ** (inve (x + 1))%xr)).
         + move => x xx /=. have -> /=: ! (lv < x + 1) by smt(). done.
       rewrite -mulr_sumr /=. done.
       apply (xle_trans ((2%r * inve (lv + 1))%xr + Ep hbino (fun (x : int) => (f n (max (x + 1) (lv + 1)))%xr))).
       + by apply xler_addr; case (0 <= lv); smt().
       apply Ep_hbino_f; 1,2:smt().
     wp; auto => &hr /=. move: (l{hr}) => {&hr} l.
     rewrite (ler_trans ((f (size l) 0)%pos + 1%r + (f (size l) 1)%pos)).
     + by smt(size_undup size_sort size_rev size_drop_while size_map f_ge0 f_incr_1 size_ge0).
     rewrite /f.
     case (size l = 0) => [ -> /= | *]. by rewrite /log2 /log ln1 /= from_int_ceil /=.
     have -> /=: 0 <= ceil (log2 (size l + 1)). by smt(size_ge0 ceil_bound log_mono ln1).
     have -> /=: 1 <= ceil (log2 (size l + 1)). by smt(size_ge0 ceil_bound log_mono ln1).
     smt(log_mono size_ge0).
   qed.

   ehoare path_length_cost : ASL.path_length : 
      (2%r * log2 (size l + 1) + 5%r)%xr ==> res%xr.
   proof.
     proc.
     (* the second loop where both h and lv get updated; we use f |dom| h + f |dom| (lv + 1) *)
     (* to bind the change in expectation of c *)
     while ((0 <= c /\ 1 <= h /\ -1 <= lv < h)
            `|` (c%r + h%r - lv%r - 1%r + f (size dom) h  + f (size dom) (lv + 1) )%xr).
     + move=> &hr /=; apply xle_cxr_r => /> *; smt(f_ge0).
     + auto => &hr /=.
     move: (h{hr}) (lv{hr}) (c{hr}) (dom{hr}) => {&hr} h lv c dom.
     rewrite if_f_cxr /=.
     rewrite Ep_cxr /=; apply xle_cxr.
     move => *. split; 1:smt(hbino_supp).
     pose n := size (behead dom).
     have *: 0 <= n. by apply size_ge0.
     have ->: size dom = n+1. by smt().
     rewrite (eq_Ep _ _
                (fun x =>
                  ((c%r - lv%r - 1%r + (max (x + 1) h)%r)%xr
                   + (f n (max (x + 1) h))%xr)
                  + (if lv < x + 1 then f n (x + 1) + 1%r else f n (lv + 1))%xr)).
     + move => x * /=. case (lv < x + 1) => * /=; apply to_realK_eq => /=; smt(f_ge0).
     rewrite !EpD.
     rewrite (Ep_hbino_shift _ h) 1:/# /=.
     rewrite (BXA.eq_big_int _ _ _
              (fun x => (inve (x + 1))%xr * (c%r + h%r - lv%r - 1%r)%xr)) 1:/#.
     rewrite BXA_mulDr bigiXR; 1:smt(inve_ge0); rewrite finsum_geo1_closed 1:/#.
     rewrite (eq_Ep _ _ (fun (x : int) => x%xr + (c%r + h%r - lv%r)%xr)).
     + move => x /hbino_supp * /=. 
       by rewrite -of_realD /#.
     rewrite EpD Ep_hbino_id EpC hbino_ll /=.
     have ->: ((1%r - inve h)%rp * (c%r + h%r - lv%r - 1%r)%rp
              + (inve h)%rp * (1%rp + (c%r + h%r - lv%r)%rp))%xr
             = (c%r + h%r - lv%r - 1%r)%xr + (2%r * inve h)%xr.
     + rewrite -of_realM; 1,2: smt(inve_le1).
       rewrite -of_realM /=; 1,2: smt(inve_ge0).
       have *: 0%r <= c%r + h%r - lv%r - 1%r. by smt().
       rewrite -of_realD /=; 1,2: smt(pmulr_rge0 inve_gt0 inve_lt1).
       rewrite -of_realD; 1,2:smt(inve_ge0).
       apply to_realK_eq => /=. rewrite !to_pos_pos; 1..4:smt(pmulr_rge0 inve_gt0 inve_lt1).
       ring.
     have -> : (c%r + h%r - lv%r - 1%r + f (n + 1) h + f (n + 1) (lv + 1))%xr
             = (c%r + h%r - lv%r - 1%r)%xr + (f (n + 1) h)%xr + (f (n + 1) (lv + 1))%xr.
     + by do 2! (rewrite /= of_realD; 1,2:smt(f_ge0)).
     rewrite -!addmA; apply xler_add2l.
     rewrite addmA; apply xler_add.
     + apply Ep_hbino_f; 1,2:smt().

     rewrite (eq_Ep _ _
               (fun (x : int) => (lv < x + 1)%xr
                 + (f n (max (x + 1) (lv + 1)))%xr)); 1: smt(of_realD f_ge0).
     rewrite EpD.
     rewrite (Ep_hbino_shift _ (lv + 1)) 1:/# /=.
     rewrite (eq_Ep _ _ (fun _ => 1%xr)); 1:smt(hbino_supp).
     rewrite EpC hbino_ll /=.
     have ->: BXA.bigi predT (fun (x : int) => ((inve (x + 1))%rp * (b2r (lv < x + 1))%rp)%xr) 0 (lv + 1)
             = (0 <= lv)%xr * (inve (lv + 1))%xr.
     + case (0 <= lv) => * /=; last first. have -> /=: lv = -1 by smt(). by smt(BXA.big_geq).
       rewrite (BXA.big_cat_int lv) 1,2:/#.
       rewrite BXA.big_int1 /=. have -> /=: lv < lv + 1 by smt().
       rewrite (BXA.eq_big_int _ _ _ (fun (x : int) => 0%r ** (inve (x + 1))%xr)).
       + move => x xx /=. have -> /=: ! (lv < x + 1) by smt(). done.
       rewrite -mulr_sumr /=. done.
     apply (xle_trans ((2%r * inve (lv + 1))%xr + Ep hbino (fun (x : int) => (f n (max (x + 1) (lv + 1)))%xr))).
     + apply xler_addr. case (0 <= lv); smt().
       apply Ep_hbino_f; 1,2:smt().

     (* the first loop where lv remains constant; we use f |dom| h + f |dom| (lv + 1) *)
     (* to bind the change in expectation of c *)
     while (let dom' = drop_while (fun k' => k < k') dom in
            (c = 0 /\ 1 <= h /\ lv = -1 /\ sorted (fun k1 k2 => K.(<=) k2 k1) dom)
            `|` ((f (size dom') 0)%xr + h%xr + (f (size dom) h)%xr)).
     + move=> &hr /=; apply xle_cxr => /> *. split; 1:smt().
       case (dom{hr} = []); 1:smt(f_ge0); smt(drop_while_head_ff f_ge0).
     + auto => &hr /=.
       move: (h{hr}) (lv{hr}) (c{hr}) (dom{hr}) (k{hr}) => {&hr} h lv c dom k.
       rewrite Ep_cxr /=; apply xle_cxr.
       move => *. split; 1: smt(hbino_supp).
       have ->: drop_while ((<) k) (behead dom) = drop_while ((<) k) dom. smt(drop_while_head_tt).
       pose m := size (drop_while ((<) k) dom).
       have *: 0 <= m. by apply size_ge0.
       pose n := size (behead dom).
       have *: 0 <= n. by apply size_ge0.
       have ->: size dom = n+1. by smt().
       rewrite (eq_Ep _ _ (fun x => (f m 0)%xr + ((max (x + 1) h)%xr
                             + (f n (max (x + 1) h))%xr))); 1:smt(addmA).
       rewrite !EpD EpC hbino_ll /=.
       have ->: ((f m 0)%rp + h%rp + (f (n + 1) h)%rp)%xr
                = (f m 0)%xr + (h%xr + (f (n + 1) h)%xr).
       + smt(of_realD f_ge0).
       apply xler_addl.
       apply (xle_trans (h%xr + ((2%r * inve h)%xr + Ep hbino (fun (x : int) => (f n (max (x + 1) h))%xr))));
                 last first. apply xler_addl; apply Ep_hbino_f; 1,2:smt().
       rewrite addmA; apply xler_addr.
   
       rewrite (Ep_hbino_shift _ h) 1:/# /=.
       rewrite (BXA.eq_big_int _ _ _ (fun x => (inve (x + 1))%xr * h%xr)) 1:/#.
       rewrite BXA_mulDr bigiXR;1:smt(inve_ge0). rewrite finsum_geo1_closed 1:/#.
       rewrite (eq_Ep _ _ (fun (x : int) => x%xr + (h%r + 1%r)%xr)).
       + move => x /hbino_supp * />.
         by rewrite -of_realD /#.
       rewrite EpD EpC Ep_hbino_id hbino_ll /=.
       rewrite !to_pos_pos; 1..5:smt(inve_le1 inve_ge0).
       have ->: (1%r - inve h) * h%r + inve h * (1%r + (h%r + 1%r)) = h%r + 2%r * inve h by ring.
       done.
     wp.
     auto => &hr /=; move: (l{hr}) (k{hr}) => {&hr} l k.

     apply xle_cxr_l => /> *. 
     + by apply rev_sorted; [apply K.le_trans | apply/sort_sorted/K.le_total].
     rewrite (ler_trans ((f (size l) 0)%pos + 1%r + (f (size l) 1)%pos)).
     smt(size_undup size_sort size_rev size_drop_while size_map f_ge0 f_incr_1 size_ge0).                
     
     rewrite /f.
     case (size l = 0) => c. rewrite c /log2 /log ln1 /= from_int_ceil /=. done.
     have -> /=: 0 <= ceil (log2 (size l + 1)). by smt(size_ge0 ceil_bound log_mono ln1). 
     have -> /=: 1 <= ceil (log2 (size l + 1)). by smt(size_ge0 ceil_bound log_mono ln1).
     smt(log_mono size_ge0).
   qed.                

   ehoare build_search : SL.build_find : 
      (2%r * log2 (size l + 1) + 5%r)%xr ==> res%xr.
   proof.
     exlim k => k_.
     conseq e_build_find (: (2%r * log2 (size l + 1) + 5%r)%xr ==> res%xr) => //; 1: smt().
     conseq build_sort_path_len  (: (2%r * log2 (size l + 1) + 5%r)%xr ==> res%xr) => //; 1: smt().
     apply path_length_cost.
   qed.

end SkipList.
