(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

module type OrderedType =
  sig
    type t
    val compare: t -> t -> int 
    val hc: int option (**)
  end

module type S =
  sig
    type key
    type !+'a t
    val empty: 'a t
    val add: key -> 'a -> 'a t -> 'a t
    val add_to_list: key -> 'a -> 'a list t -> 'a list t
    val update: key -> ('a option -> 'a option) -> 'a t -> 'a t
    val singleton: key -> 'a -> 'a t
    val remove: key -> 'a t -> 'a t
    val merge:
      (key -> 'a option -> 'b option -> 'c option) ->
      'a t -> 'b t -> 'c t
    val union: (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    val cardinal: 'a t -> int
    val size: 'a t -> int (**)
    val bindings: 'a t -> (key * 'a) list
    val min_binding: 'a t -> (key * 'a)
    val min_binding_opt: 'a t -> (key * 'a) option
    val max_binding: 'a t -> (key * 'a)
    val max_binding_opt: 'a t -> (key * 'a) option
    val choose: 'a t -> (key * 'a)
    val choose_opt: 'a t -> (key * 'a) option
    val find: key -> 'a t -> 'a
    val find_opt: key -> 'a t -> 'a option
    val find_first: (key -> bool) -> 'a t -> key * 'a
    val find_first_opt: (key -> bool) -> 'a t -> (key * 'a) option
    val find_last: (key -> bool) -> 'a t -> key * 'a
    val find_last_opt: (key -> bool) -> 'a t -> (key * 'a) option
    val iter: (key -> 'a -> unit) -> 'a t -> unit
    val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val map: ('a -> 'b) -> 'a t -> 'b t
    val mapi: (key -> 'a -> 'b) -> 'a t -> 'b t
    val filter: (key -> 'a -> bool) -> 'a t -> 'a t
    val filter_map: (key -> 'a -> 'b option) -> 'a t -> 'b t
    val partition: (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val split: key -> 'a t -> 'a t * 'a option * 'a t
    val is_empty: 'a t -> bool
    val mem: key -> 'a t -> bool
    val equal: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val compare: ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val for_all: (key -> 'a -> bool) -> 'a t -> bool
    val exists: (key -> 'a -> bool) -> 'a t -> bool
    val to_list : 'a t -> (key * 'a) list
    val of_list : (key * 'a) list -> 'a t
    val to_seq : 'a t -> (key * 'a) Seq.t
    val to_rev_seq : 'a t -> (key * 'a) Seq.t
    val to_seq_from : key -> 'a t -> (key * 'a) Seq.t
    val add_seq : (key * 'a) Seq.t -> 'a t -> 'a t
    val of_seq : (key * 'a) Seq.t -> 'a t
  end

module Make(Ord: OrderedType) = struct

    type key = Ord.t

    let () = 
      match Ord.hc with
      | Some n when n <= 0 -> 
          invalid_arg "smap.ml: hc must be a positive integer" 
      | _ -> 
          ()

    type 'a t = 
        Empty
      | Node of  {l:'a t; v:key; d:'a; r:'a t; h:int}
      | SNode of {l:'a t; v:key; d:'a; r:'a t; h:int; s:int}

    let height = function 
        Empty     -> 0
      | Node {h}  -> h
      | SNode {h} -> h

    let rec size = function
        Empty       -> 0
      | Node {l; r} -> size l + 1 + size r
      | SNode {s}   -> s

    let make_node l x d r ht s =
      let is_snode = match Ord.hc with
      | Some n -> ht mod n = 0
      | None   -> false in
      match s with
      | Some s0 -> 
          if is_snode then SNode{l; v=x; d; r; h=ht; s=s0}
          else Node{l; v=x; d; r; h=ht}
      | None    -> 
          if is_snode then SNode{l; v=x; d; r; h=ht; s=(size l + 1 + size r)}
          else Node{l; v=x; d; r; h=ht}

    let create l x d r = 
      let hl = height l 
      and hr = height r in
        let ht = (if hl >= hr then hl + 1 else hr + 1) in
          make_node l x d r ht None

    let s_create l x d r s =
      let hl = height l 
      and hr = height r in
        let ht = (if hl >= hr then hl + 1 else hr + 1) in
          make_node l x d r ht (Some s)

    let singleton x d =
      match Ord.hc with
      | Some n when n = 1 ->
          SNode{l=Empty; v=x; d; r=Empty; h=1; s=1}
      | _  ->
          Node{l=Empty; v=x; d; r=Empty; h=1}

    (*maybe creating an s_bal as well is optimal, I'll cross that road when I get there*)
    let bal l x d r =
      let hl = match l with 
        Empty -> 0 
      | Node {h} | SNode {h} -> h in
      let hr = match r with 
        Empty -> 0 
      | Node {h} | SNode {h} -> h in
      let is_snode = match Ord.hc with
      | Some n -> ((if hl >= hr then hl + 1 else hr + 1) mod n = 0)
      | None   -> false in
      if hl > hr + 2 then begin
        match l with
          Empty -> invalid_arg "Map.bal"
        | Node{l=ll; v=lv; d=ld; r=lr} ->
            if height ll >= height lr then
              create ll lv ld (create lr x d r)
            else begin
              match lr with
                Empty -> invalid_arg "Map.bal"
              | Node{l=lrl; v=lrv; d=lrd; r=lrr} ->
                  create (create ll lv ld lrl) lrv lrd (create lrr x d r)
              | SNode{l=lrl; v=lrv; d=lrd; r=lrr; s=lrs} ->
                  (*check if lrs can be used*)
                  let nl = create ll lv ld lrl
                  and nr = create lrr x d r in
                  if is_snode then s_create nl lrv lrd nr (lrs + size ll + 2 + size r)
                  else create nl lrv lrd nr
            end
        | SNode{l=ll; v=lv; d=ld; r=lr; s=ls} ->
            if height ll >= height lr then
              (*check if ls can be used*)
              let nr = create lr x d r in
              if is_snode then s_create ll lv ld nr (ls + 1 + size r)
              else create ll lv ld nr
            else begin (*if we are in an SNode, lrs does not provide any valuable information*)
              (*Check if ls can be used*)
              match lr with
              Empty -> invalid_arg "Map.bal"
            | Node{l=lrl; v=lrv; d=lrd; r=lrr} ->
                let nl = create ll lv ld lrl
                and nr = create lrr x d r in
                if is_snode then s_create nl lrv lrd nr (ls + 1 + size r)
                else create nl lrv lrd nr 
            | SNode{l=lrl; v=lrv; d=lrd; r=lrr} ->
                let nl = create ll lv ld lrl
                and nr = create lrr x d r in
                if is_snode then s_create nl lrv lrd nr (ls + 1 + size r)
                else create nl lrv lrd nr 
            end
      end else if hr > hl + 2 then begin
        match r with
          Empty -> invalid_arg "Map.bal"
        | Node{l=rl; v=rv; d=rd; r=rr} ->
            if height rr >= height rl then
              create (create l x d rl) rv rd rr
            else begin
              match rl with
              Empty -> invalid_arg "Map.bal"
            | Node{l=rll; v=rlv; d=rld; r=rlr} ->
                create (create l x d rll) rlv rld (create rlr rv rd rr)
            | SNode{l=rll; v=rlv; d=rld; r=rlr; s=rls} ->
                (*Check if rls can be used*)
                let nl = create l x d rll
                and nr = create rlr rv rd rr in
                if is_snode then s_create nl rlv rld nr (size l + 2 + size rr + rls)
                else create nl rlv rld nr
        | SNode{l=rl; v=rv; d=rd; r=rr; s=rs} ->
            if height rr >= height rl then
              let nl = create l x d rl in
              if is_snode then s_create nl rv rd rr (size l + 1 + rs)
              else create nl rv rd rr
            else begin
              (*check if rs can be used, again no use for rls*)
              match rl with
                Empty -> invalid_arg "Map.bal"
              | Node{l=rll; v=rlv; d=rld; r=rlr} ->
                  let nl = create l x d rll
                  and nr = create rlr rv rd rr in
                  if is_snode then s_create nl rlv rld nr (size l + 2 + size rr + rls)
                  else create nl rlv rld nr
              | SNode{l=rll; v=rlv; d=rld; r=rlr} ->
                  let nl = create l x d rll
                  and nr = create rlr rv rd rr in
                  if is_snode then s_create nl rlv rld nr (size l + 2 + size rr + rls)
                  else create nl rlv rld nr
            end
      end else
        let ht = (if hl >= hr then hl + 1 else hr + 1) in
          if is_snode then 
            make_node l x d r ht (Some (size l + 1 + size r))
          else 
            make_node l x d r ht None

    let s_bal l x d r s =
      let hl = match l with 
        Empty -> 0 
      | Node {h} | SNode {h} -> h in
      let hr = match r with 
        Empty -> 0 
      | Node {h} | SNode {h} -> h in
      let is_snode = match Ord.hc with
      | Some n -> ((if hl >= hr then hl + 1 else hr + 1) mod n = 0)
      | None   -> false in
      if hl > hr + 2 then begin
        match l with
          Empty -> invalid_arg "Map.bal"
        | Node{l=ll; v=lv; d=ld; r=lr}
        | SNode{l=ll; v=lv; d=ld; r=lr} ->
            if height ll >= height lr then
              if is_snode then s_create ll lv ld (create lr x d r) s
              else create ll lv ld nr
            else begin 
              match lr with
              Empty -> invalid_arg "Map.bal"
            | Node{l=lrl; v=lrv; d=lrd; r=lrr}
            | SNode{l=lrl; v=lrv; d=lrd; r=lrr} ->
                if is_snode then s_create (create ll lv ld lrl) lrv lrd (create lrr x d r) s
                else create nl lrv lrd nr 
            end
      end else if hr > hl + 2 then begin
        match r with
          Empty -> invalid_arg "Map.bal"
        | Node{l=rl; v=rv; d=rd; r=rr} 
        | SNode{l=rl; v=rv; d=rd; r=rr} ->
            if height rr >= height rl then
              if is_snode then s_create (create l x d rl) rv rd rr s
              else create (create l x d rl) rv rd rr
            else begin
              match rl with
              Empty -> invalid_arg "Map.bal"
            | Node{l=rll; v=rlv; d=rld; r=rlr}
            | SNode{l=rll; v=rlv; d=rld; r=rlr} ->
                if is_snode then s_create (create l x d rll) rlv rld (create rlr rv rd rr) s
                else create (create l x d rll) rlv rld (create rlr rv rd rr)
            end
      end else
        let ht = (if hl >= hr then hl + 1 else hr + 1) in
          if is_snode then 
            make_node l x d r ht (Some s)
          else 
            make_node l x d r ht None
            
    let empty = Empty

    let is_empty = function Empty -> true | _ -> false

    let rec add x data = function
        Empty ->
          make_node Empty x data Empty 1 (Some 1)
      | Node {l; v; d; r; h} ->
          let c = Ord.compare x v in
          if c = 0 then
            if d == data then make_node l v d r h None
            else make_node l x data r h None
          else if c < 0 then
            let ll = add x data l in
            if l == ll then make_node l v d r h None
            else bal ll v d r
          else
            let rr = add x data r in
            if r == rr then make_node l v d r h
            else bal l v d rr
      | SNode {l; v; d; r; h; s} as m ->
          let c = Ord.compare x v in
          if c = 0 then
            if d == data then make_node l v d r h (Some s)
            else make_node l x data r h (Some s)
          else if c < 0 then
            let ll = add x data l in
            if l == ll then make_node l v d r h (Some s)
            else s_bal ll v d r s
          else
            let rr = add x data r in
            if r == rr then m else s_bal l v d rr s

    let rec find x = function
        Empty ->
          raise Not_found
      | Node {l; v; d; r}
      | SNode{l; v; d; r} ->
          let c = Ord.compare x v in
          if c = 0 then d
          else find x (if c < 0 then l else r)

    let rec find_first_aux v0 d0 f = function
        Empty ->
          (v0, d0)
      | Node {l; v; d; r}
      | SNode{l; v; d; r} ->    
          if f v then
            find_first_aux v d f l
          else
            find_first_aux v0 d0 f r

    let rec find_first f = function
        Empty ->
          raise Not_found
      | Node {l; v; d; r}
      | SNode{l; v; d; r} ->
          if f v then
            find_first_aux v d f l
          else
            find_first f r

    let rec find_first_opt_aux v0 d0 f = function
        Empty ->
          Some (v0, d0)
      | Node {l; v; d; r}
      | SNode{l; v; d; r} ->
          if f v then
            find_first_opt_aux v d f l
          else
            find_first_opt_aux v0 d0 f r

    let rec find_first_opt f = function
        Empty ->
          None
      | Node {l; v; d; r}
      | SNode{l; v; d; r} ->
          if f v then
            find_first_opt_aux v d f l
          else
            find_first_opt f r

    let rec find_last_aux v0 d0 f = function
        Empty ->
          (v0, d0)
      | Node {l; v; d; r}
      | SNode{l; v; d; r} ->
          if f v then
            find_last_aux v d f r
          else
            find_last_aux v0 d0 f l

    let rec find_last f = function
        Empty ->
          raise Not_found
      | Node {l; v; d; r}
      | SNode{l; v; d; r} ->
          if f v then
            find_last_aux v d f r
          else
            find_last f l

    let rec find_last_opt_aux v0 d0 f = function
        Empty ->
          Some (v0, d0)
      | Node {l; v; d; r}
      | SNode{l; v; d; r} ->
          if f v then
            find_last_opt_aux v d f r
          else
            find_last_opt_aux v0 d0 f l

    let rec find_last_opt f = function
        Empty ->
          None
      | Node {l; v; d; r}
      | SNode{l; v; d; r} ->
          if f v then
            find_last_opt_aux v d f r
          else
            find_last_opt f l

    let rec find_opt x = function
        Empty ->
          None
      | Node {l; v; d; r}
      | SNode{l; v; d; r} ->
          let c = Ord.compare x v in
          if c = 0 then Some d
          else find_opt x (if c < 0 then l else r)

    let rec mem x = function
        Empty ->
          false
      | Node {l; v; r}
      | SNode{l; v; r} ->
          let c = Ord.compare x v in
          c = 0 || mem x (if c < 0 then l else r)

    let rec min_binding = function
        Empty -> raise Not_found
      | Node {l=Empty; v; d} 
      | SNode{l=Empty; v; d} -> (v, d)
      | Node {l} | SNode {l} -> min_binding l

    let rec min_binding_opt = function
        Empty -> None
      | Node {l=Empty; v; d}
      | SNode{l=Empty; v; d} -> Some (v, d)
      | Node {l} | SNode {l} -> min_binding_opt l

    let rec max_binding = function
        Empty -> raise Not_found
      | Node {v; d; r=Empty} 
      | SNode{v; d; r=Empty} -> (v, d)
      | Node {r} | SNode {r} -> max_binding r

    let rec max_binding_opt = function
        Empty -> None
      | Node {v; d; r=Empty}
      | SNode{v; d; r=Empty} -> Some (v, d)
      | Node {r} | SNode {r} -> max_binding_opt r

    let rec remove_min_binding = function
        Empty -> invalid_arg "Map.remove_min_elt"
      | Node {l=Empty; r} 
      | SNode{l=Empty; r}       -> r
      | Node {l; v; d; r}       -> bal (remove_min_binding l) v d r
      | SNode{l; v; d; r; s=sz} -> s_bal (remove_min_binding l) v d r (sz - 1)

    let merge t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) ->
          let (x, d) = min_binding t2 in
          bal t1 x d (remove_min_binding t2)

    let s_merge t1 t2 s =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) ->
          let (x, d) = min_binding t2 in
          s_bal t1 x d (remove_min_binding t2) s

    let rec remove x = function
        Empty ->
          Empty
      | (Node {l; v; d; r} as m) ->
          let c = Ord.compare x v in
          if c = 0 then merge l r
          else if c < 0 then
            let ll = remove x l in if l == ll then m else bal ll v d r
          else
            let rr = remove x r in if r == rr then m else bal l v d rr
      | (SNode{l; v; d; r; s=sz} as m) ->
          let c = Ord.compare x v in
          if c = 0 then s_merge l r (sz-1)
          else if c < 0 then
            let ll = remove x l in if l == ll then m else s_bal ll v d r (sz-1)
          else
            let rr = remove x r in if r == rr then m else s_bal l v d rr (sz-1)
(**)
    let rec update x f = function
        Empty ->
          begin match f None with
          | None -> Empty
          | Some data -> Node{l=Empty; v=x; d=data; r=Empty; h=1}
          end
      | Node {l; v; d; r; h} as m ->
          let c = Ord.compare x v in
          if c = 0 then begin
            match f (Some d) with
            | None -> merge l r
            | Some data ->
                if d == data then m else Node{l; v=x; d=data; r; h}
          end else if c < 0 then
            let ll = update x f l in
            if l == ll then m else bal ll v d r
          else
            let rr = update x f r in
            if r == rr then m else bal l v d rr

    let add_to_list x data m =
      let add = function None -> Some [data] | Some l -> Some (data :: l) in
      update x add m

    let rec iter f = function
        Empty -> ()
      | Node {l; v; d; r} ->
          iter f l; f v d; iter f r

    let rec map f = function
        Empty ->
          Empty
      | Node {l; v; d; r; h} ->
          let l' = map f l in
          let d' = f d in
          let r' = map f r in
          Node{l=l'; v; d=d'; r=r'; h}

    let rec mapi f = function
        Empty ->
          Empty
      | Node {l; v; d; r; h} ->
          let l' = mapi f l in
          let d' = f v d in
          let r' = mapi f r in
          Node{l=l'; v; d=d'; r=r'; h}

    let rec fold f m accu =
      match m with
        Empty -> accu
      | Node {l; v; d; r} ->
          fold f r (f v d (fold f l accu))

    let rec for_all p = function
        Empty -> true
      | Node {l; v; d; r} -> p v d && for_all p l && for_all p r

    let rec exists p = function
        Empty -> false
      | Node {l; v; d; r} -> p v d || exists p l || exists p r

    (* Beware: those two functions assume that the added k is *strictly*
       smaller (or bigger) than all the present keys in the tree; it
       does not test for equality with the current min (or max) key.

       Indeed, they are only used during the "join" operation which
       respects this precondition.
    *)

    let rec add_min_binding k x = function
      | Empty -> singleton k x
      | Node {l; v; d; r} ->
        bal (add_min_binding k x l) v d r

    let rec add_max_binding k x = function
      | Empty -> singleton k x
      | Node {l; v; d; r} ->
        bal l v d (add_max_binding k x r)

    (* Same as create and bal, but no assumptions are made on the
       relative heights of l and r. *)

    let rec join l v d r =
      match (l, r) with
        (Empty, _) -> add_min_binding v d r
      | (_, Empty) -> add_max_binding v d l
      | (Node{l=ll; v=lv; d=ld; r=lr; h=lh},
         Node{l=rl; v=rv; d=rd; r=rr; h=rh}) ->
          if lh > rh + 2 then bal ll lv ld (join lr v d r) else
          if rh > lh + 2 then bal (join l v d rl) rv rd rr else
          create l v d r

    (* Merge two trees l and r into one.
       All elements of l must precede the elements of r.
       No assumption on the heights of l and r. *)

    let concat t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) ->
          let (x, d) = min_binding t2 in
          join t1 x d (remove_min_binding t2)

    let concat_or_join t1 v d t2 =
      match d with
      | Some d -> join t1 v d t2
      | None -> concat t1 t2

    let rec split x = function
        Empty ->
          (Empty, None, Empty)
      | Node {l; v; d; r} ->
          let c = Ord.compare x v in
          if c = 0 then (l, Some d, r)
          else if c < 0 then
            let (ll, pres, rl) = split x l in (ll, pres, join rl v d r)
          else
            let (lr, pres, rr) = split x r in (join l v d lr, pres, rr)

    let rec merge f s1 s2 =
      match (s1, s2) with
        (Empty, Empty) -> Empty
      | (Node {l=l1; v=v1; d=d1; r=r1; h=h1}, _) when h1 >= height s2 ->
          let (l2, d2, r2) = split v1 s2 in
          concat_or_join (merge f l1 l2) v1 (f v1 (Some d1) d2) (merge f r1 r2)
      | (_, Node {l=l2; v=v2; d=d2; r=r2}) ->
          let (l1, d1, r1) = split v2 s1 in
          concat_or_join (merge f l1 l2) v2 (f v2 d1 (Some d2)) (merge f r1 r2)
      | _ ->
          assert false

    let rec union f s1 s2 =
      match (s1, s2) with
      | (Empty, s) | (s, Empty) -> s
      | (Node {l=l1; v=v1; d=d1; r=r1; h=h1},
         Node {l=l2; v=v2; d=d2; r=r2; h=h2}) ->
          if h1 >= h2 then
            let (l2, d2, r2) = split v1 s2 in
            let l = union f l1 l2 and r = union f r1 r2 in
            match d2 with
            | None -> join l v1 d1 r
            | Some d2 -> concat_or_join l v1 (f v1 d1 d2) r
          else
            let (l1, d1, r1) = split v2 s1 in
            let l = union f l1 l2 and r = union f r1 r2 in
            match d1 with
            | None -> join l v2 d2 r
            | Some d1 -> concat_or_join l v2 (f v2 d1 d2) r

    let rec filter p = function
        Empty -> Empty
      | Node {l; v; d; r} as m ->
          (* call [p] in the expected left-to-right order *)
          let l' = filter p l in
          let pvd = p v d in
          let r' = filter p r in
          if pvd then if l==l' && r==r' then m else join l' v d r'
          else concat l' r'

    let rec filter_map f = function
        Empty -> Empty
      | Node {l; v; d; r} ->
          (* call [f] in the expected left-to-right order *)
          let l' = filter_map f l in
          let fvd = f v d in
          let r' = filter_map f r in
          begin match fvd with
            | Some d' -> join l' v d' r'
            | None -> concat l' r'
          end

    let rec partition p = function
        Empty -> (Empty, Empty)
      | Node {l; v; d; r} ->
          (* call [p] in the expected left-to-right order *)
          let (lt, lf) = partition p l in
          let pvd = p v d in
          let (rt, rf) = partition p r in
          if pvd
          then (join lt v d rt, concat lf rf)
          else (concat lt rt, join lf v d rf)

    type 'a enumeration = End | More of key * 'a * 'a t * 'a enumeration

    let rec cons_enum m e =
      match m with
        Empty -> e
      | Node {l; v; d; r} -> cons_enum l (More(v, d, r, e))

    let compare cmp m1 m2 =
      let rec compare_aux e1 e2 =
          match (e1, e2) with
          (End, End) -> 0
        | (End, _)  -> -1
        | (_, End) -> 1
        | (More(v1, d1, r1, e1), More(v2, d2, r2, e2)) ->
            let c = Ord.compare v1 v2 in
            if c <> 0 then c else
            let c = cmp d1 d2 in
            if c <> 0 then c else
            compare_aux (cons_enum r1 e1) (cons_enum r2 e2)
      in compare_aux (cons_enum m1 End) (cons_enum m2 End)

    let equal cmp m1 m2 =
      let rec equal_aux e1 e2 =
          match (e1, e2) with
          (End, End) -> true
        | (End, _)  -> false
        | (_, End) -> false
        | (More(v1, d1, r1, e1), More(v2, d2, r2, e2)) ->
            Ord.compare v1 v2 = 0 && cmp d1 d2 &&
            equal_aux (cons_enum r1 e1) (cons_enum r2 e2)
      in equal_aux (cons_enum m1 End) (cons_enum m2 End)

    let rec cardinal = function
        Empty -> 0
      | Node {l; r} -> cardinal l + 1 + cardinal r

    let rec bindings_aux accu = function
        Empty -> accu
      | Node {l; v; d; r} -> bindings_aux ((v, d) :: bindings_aux accu r) l

    let bindings s =
      bindings_aux [] s

    let choose = min_binding

    let choose_opt = min_binding_opt

    let to_list = bindings
    let of_list bs = List.fold_left (fun m (k, v) -> add k v m) empty bs

    let add_seq i m =
      Seq.fold_left (fun m (k,v) -> add k v m) m i

    let of_seq i = add_seq i empty

    let rec seq_of_enum_ c () = match c with
      | End -> Seq.Nil
      | More (k,v,t,rest) -> Seq.Cons ((k,v), seq_of_enum_ (cons_enum t rest))

    let to_seq m =
      seq_of_enum_ (cons_enum m End)

    let rec snoc_enum s e =
      match s with
        Empty -> e
      | Node{l; v; d; r} -> snoc_enum r (More(v, d, l, e))

    let rec rev_seq_of_enum_ c () = match c with
      | End -> Seq.Nil
      | More (k,v,t,rest) ->
          Seq.Cons ((k,v), rev_seq_of_enum_ (snoc_enum t rest))

    let to_rev_seq c =
      rev_seq_of_enum_ (snoc_enum c End)

    let to_seq_from low m =
      let rec aux low m c = match m with
        | Empty -> c
        | Node {l; v; d; r; _} ->
            begin match Ord.compare v low with
              | 0 -> More (v, d, r, c)
              | n when n<0 -> aux low r c
              | _ -> aux low l (More (v, d, r, c))
            end
      in
      seq_of_enum_ (aux low m End)
end
