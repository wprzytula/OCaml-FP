(*
 * ISet - Interval sets
 * Copyright (C) 1996-2019 Xavier Leroy, Nicolas Cannasse, Markus Mottl,
   Jacek Chrzaszcz, Wojciech Przytula
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version,
 * with the special exception on linking described in file LICENSE.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

(** Interval Set.
    This is an interval set, i.e. a set of integers, where large
    intervals can be stored as single elements. Intervals stored in the
    set are disjoint. 
*)

(* AUTOR - WOJCIECH PRZYTUŁA     *)
(* REVIEWER - MATEUSZ NOWAKOWSKI *)


(* Typ drzewa przedziałów *)
type t = 
  | Empty
  | Node of t * (int * int) * t * int * int


(* height: t -> int                   *)
(* zwraca wysokość zadanego poddrzewa *)
let height = function
  | Node (_, _, _, h, _) -> h
  | Empty -> 0
  
  
(* quan : t -> int                                              *)
(* zwraca liczbę elementów we wszystkich przedziałach poddrzewa *)
let quan = function
  | Empty -> 0
  | Node (_, _, _, _, q) -> q


(* big_sum : int -> int -> int                                   *)
(* zwraca sumę dwóch liczb całkowitych z uwzględnieniem operacji *)
(* na krańcowych wartościach typu liczb całkowitych              *)
let big_sum a b =
  if a >= 0 && b >= 0 then
    if a + b < a || a + b < b then max_int else a + b
  else if a < 0 && b < 0 then
    if a + b > a || a + b > b then min_int else a + b
  else a + b
  
  
(* big_diff : int -> int -> int                                     *)
(* zwraca różnicę dwóch liczb całkowitych z uwzględnieniem operacji *)
(* na krańcowych wartościach typu liczb całkowitych                 *)
let big_diff a b =
  if a = b then 0
  else if a < 0 && b > 0 then
    if a - b > a then min_int else a - b
  else if a >= 0 && b < 0 then 
    if a - b < a then max_int else a - b
  else a - b


(* count : int * int -> int                       *)
(* zwraca liczbę elementów zawartych w przedziale *)
let count (k1, k2) =
  big_sum (big_diff k2 k1) 1


(* make : t -> int * int -> t -> t                              *)
(* zwraca drzewo na podstawie dwóch poddrzew i wartości w węźle *)
let make l k r = 
  Node (l, k, r, max (height l) (height r) + 1,
        big_sum (big_sum (quan l) (quan r)) (count k))


(* bal : t -> int * int -> t -> t    *)
(* przeprowadza pojedynczą operację  *)
(* balansowania jeśli jest konieczna *)
let bal l k r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _, _) ->
        if height ll >= height lr then make ll lk (make lr k r)
        else
          (match lr with
          | Node (lrl, lrk, lrr, _, _) ->
              make (make ll lk lrl) lrk (make lrr k r)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _, _) ->
        if height rr >= height rl then make (make l k rl) rk rr
        else
          (match rl with
          | Node (rll, rlk, rlr, _, _) ->
              make (make l k rll) rlk (make rlr rk rr)
          | Empty -> assert false)
    | Empty -> assert false
  else Node (l, k, r, max hl hr + 1, 
            big_sum (big_sum (quan l) (quan r)) (count k))


(* bal_subset : t -> t                  *)
(* robi to co bal, ale przyjmuje drzewo *)
let bal_subset = function
  | Empty -> Empty
  | Node (l, k, r, _, _) -> bal l k r
  
  
(* bal_loop : t -> t                                      *)
(* powtarza balansowanie na danym poddrzewie "do skutku", *)
(* czyli do uzyskania odpowiedniego zbalansowania         *)
let rec bal_loop = function
  | Empty -> Empty
  | Node (l, _, r, _, _) as set ->
      let new_set = bal_subset set in
      match new_set with
      | Empty -> Empty
      | Node(l, _, r, _, _) -> 
        let hl = height l and hr = height r in
        if hl > hr + 2 || hr > hl + 2
        then bal_loop new_set
        else set
  
  
(* min_elt : t -> int                   *)
(* zwraca najmniejszy element w zbiorze *)
let rec min_elt = function
  | Node (Empty, k, _, _, _) -> k
  | Node (l, _, _, _, _) -> min_elt l
  | Empty -> raise Not_found


(* remove_min_elt : t -> t                         *)
(* zwraca drzewo pozbawione najmniejszego elementu *)
let rec remove_min_elt = function
  | Node (Empty, _, r, _, _) -> r
  | Node (l, k, r, _, _) -> bal (remove_min_elt l) k r
  | Empty -> invalid_arg "iSet.remove_min_elt"


(* merge : t -> t -> t                          *)
(* zwraca połączenie dwóch rozłącznych zbiorów, *)
(* zakłada że elementy w t1 < elementy w t2     *)
let merge t1 t2 =
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
      let k = min_elt t2 in
      bal_loop (Node(t1, k, (remove_min_elt t2), (-1),
                big_sum(big_sum (quan t1) (quan t2)) (count k)))


(* empty : t   *)
(* pusty zbiór *)
let empty = Empty


(* is_empty : t -> bool    *)
(* zwraca true jeśli zbiór *)
(* jest pusty i false wpp  *)
let is_empty x = 
  x = Empty


(* add_helper : int -> int -> bool -> t -> int * t * int            *)
(* zwraca krotkę [new_branch, new_k, new_h], gdzie w zależności     *)
(* od [seek_k1], [new_branch] i [new_k] są odpowiednio lewą gałęzią *)
(* i lewym ograniczeniem (dla true) lub prawą gałęzią i             *)
(* prawym ograniczeniem (dla false) drzewa, na którym pierwotnie    *)
(* został wywołany add_helper, zaś [new_h] jest jego wysokością.    *)
let rec add_helper x1 x2 seek_k2 = function
  | Empty -> 
    if not seek_k2 then (x1, Empty, 0) else (x2, Empty, 0)
  | Node (l, (k1, k2), r, h, _) -> 
    let c_x1k1 = big_diff (big_diff x1 1) k1
    and c_x1k2 = big_diff (big_diff x1 1) k2
    and c_x2k1 = big_diff (big_sum x2 1) k1
    and c_x2k2 = big_diff (big_sum x2 1) k2 in
  
    if not seek_k2 then
        if c_x1k2 > 0 then
          let (rk, r, rh) = add_helper x1 x2 seek_k2 r
          and new_h = max (height l) (height r) + 1 in
          (min x1 rk, Node (l, (k1, k2), r, new_h,
                            big_sum (big_sum (quan r) (quan l))
                                    (count (k1, k2))), new_h)
        else
          if c_x1k1 < 0 then
            let (lk, l, lh) = add_helper x1 x2 seek_k2 l in
            (min lk k1, l, max (height l) (height r))
          else (k1, l, max (height l) (height r))
    else
        if c_x2k1 < 0 then
          let (lk, l, lh) = add_helper x1 x2 seek_k2 l
          and new_h = max (height l) (height r) + 1 in
          (max x2 lk, Node (l, (k1, k2), r, new_h,
                            big_sum (big_sum (quan r) (quan l))
                                    (count (k1, k2))), new_h)
        else 
          if c_x2k2 > 0 then
            let (rk, r, rh) = add_helper x1 x2 seek_k2 r in
            (max rk k2, r, max (height l) (height r))
          else (k2, r, max (height l) (height r))
   
   
(*  add : int * int -> t -> t                                       *)
(* [add (x, y) s] zwraca zbiór zawierający te same elementy co [s], *)
(* oraz wszystkie elementy ze zbioru [[x,y]], w tym [x] and [y].    *)
(* Zakłada że [x <= y].                                             *)
let rec add (x1, x2) = function
  | Empty -> Node (Empty, (x1, x2), Empty, 1, count (x1, x2))
  | Node (l, (k1, k2), r, _, _) as curr ->
    let lh = height l and rh = height r in
   
    let c_x1k1 = big_diff (big_diff x1 1) k1
    and c_x1k2 = big_diff (big_diff x1 1) k2
    and c_x2k1 = big_diff (big_sum x2 1) k1
    and c_x2k2 = big_diff (big_sum x2 1) k2 in
   
    if c_x1k1 >= 0 && c_x2k2 <= 0 then curr
    else if c_x2k1 < 0 then
      let new_l = add (x1, x2) l in
      let new_lh = height new_l in
      bal_loop (Node (new_l, (k1, k2), r, max new_lh rh + 1,
                      big_sum (big_sum (quan new_l) (quan r))
                               (count (k1, k2))))
    else if c_x1k2 > 0 then
      let new_r = add (x1, x2) r in
      let new_rh = height new_r in
      bal_loop (Node (l, (k1, k2), new_r, max lh new_rh + 1, 
                      big_sum (big_sum (quan l) (quan new_r))
                               (count (k1, k2))))
    else if c_x1k1 >= 0 then
      let (new_rk, new_r, new_rh) = add_helper x1 x2 true r in
      bal_loop (Node (l, (k1, new_rk), new_r, 
                      max (max new_rh rh) lh + 1, 
                      big_sum (big_sum (quan l) (quan new_r))
                               (count (k1, k2))))
    else if c_x2k2 <= 0 then
      let (new_lk, new_l, new_lh) = add_helper x1 x2 false l in
      bal_loop (Node(new_l, (new_lk, k2), r, 
                   max (max new_lh lh) rh + 1,
                   big_sum (big_sum (quan new_l) (quan r))
                            (count (new_lk, k2))))
    else
      let (new_lk, new_l, new_lh) = add_helper x1 x2 false l
      and (new_rk, new_r, new_rh) = add_helper x1 x2 true r in
      bal_loop (Node (new_l, (new_lk, new_rk), new_r, 
                      max (max new_lh lh) (max new_rh rh) + 1,
                      big_sum (big_sum (quan new_l) (quan new_r))
                               (count (k1, k2))))
                               
      
(* join : t -> int * int -> t -> t                           *)
(* zwraca zbiór będący połączeniem dwóch rozłącznych zbiorów *)
(* poprzez węzeł zawierający wartość zadany przedział        *)
let rec join l v r =
  match (l, r) with
  | (Empty, _) -> add v r
  | (_, Empty) -> add v l
  | (Node(ll, lv, lr, lh, lq), Node(rl, rv, rr, rh, rq)) ->
      if lh > rh + 2 
        then bal_loop (Node(ll, lv, (join lr v r), (-1),
                            big_sum (big_sum lq rq) (count v)))
      else if rh > lh + 2 
        then bal_loop (Node((join l v rl), rv, rr, (-1),
                             big_sum (big_sum lq rq) (count v)))
      else
        make l v r


(* split : int -> t -> t * bool * t                             *)
(* dla argumentów [x] [set]                                     *)  
(* zwraca krotkę postaci [l] [pres] [r],                        *)
(* gdzie [l] to zbiór wszystkich elementów mniejszych od [x],   *)
(* [r] to zbiór wszystkich elementów większych od [x],          *)
(* natomiast [pres] określa czy element [x] znajdował się       *)
(* w wejściowym zbiorze [set]                                   *)
let split x set =
  let rec loop x = function
    | Empty ->
        (Empty, false, Empty)
    | Node (l, (k1, k2), r, _, _) ->
        let ck1 = x - k1
        and ck2 = x - k2 in
        if ck1 < 0 
          then let (ll, pres, rl) = 
            loop x l in (ll, pres, join rl (k1, k2) r)
        else if ck2 > 0
          then let (lr, pres, rr) = 
            loop x r in (join l (k1, k2) lr, pres, rr)
        else
          if ck1 = 0 && ck2 = 0 then
            (l, true, r)
          else if ck1 = 0 then
            (l, true, add (big_sum x 1, k2) r)
          else if ck2 = 0 then
            (add (k1, big_diff x 1) l, true, r)
          else
            (add (k1, big_diff x 1) l, true, add (big_sum x 1, k2) r)
  in
  let setl, pres, setr = loop x set in
  (setl, pres, setr)


(* rem_helper : int -> int -> bool -> bool -> t -> t             *)
(* zwraca nowe poddrzewem po usunięciu z niego elementów         *)
(* zawartych w przedziale [x1, x2]. Flaga [seek_k1] determinuje  *)
(* czy rem_helper działa na lewej (true), czy na prawej (false)  *)
(* gałęzi zadanego pierwotnie poddrzewa, natomiast flaga [found] *)
(* powinna być wyjściowo ustawiona na [false].                   *)
let rec rem_helper x1 x2 seek_k1 found = function
  | Empty -> Empty
  | Node (l, (k1, k2), r, _, _) -> 
    let c_x1k1 = big_diff x1 k1
    and c_x1k2 = big_diff x1 k2
    and c_x2k1 = big_diff x2 k1
    and c_x2k2 = big_diff x2 k2 in
    
    if not found then
      if seek_k1 then
        if c_x1k2 > 0 then
          let new_r = rem_helper x1 x2 true true r in
          Node (l, (k1, k2), new_r, max (height new_r) (height l) + 1,
                big_sum (big_sum (quan l) (quan new_r))
                         (count (k1, k2)))
        else if c_x1k1 < 0 then rem_helper x1 x2 true false l
        else if c_x1k1 = 0 then l
        else if c_x1k1 > 0 then 
          Node (l, (k1, big_diff x1 1), Empty, height l + 1,
                big_sum (quan l) (count (k1, big_diff x1 1)))
        else assert false
      else
        if c_x2k1 < 0 then
          let new_l = rem_helper x1 x2 false true l in
          Node (new_l, (k1, k2), r, max (height new_l) (height r) + 1,
                quan new_l + quan r + count (k1, k2))
        else if c_x2k2 > 0 then rem_helper x1 x2 false false r
        else if c_x2k2 = 0 then r
        else if c_x1k1 < 0 then 
          Node (Empty, (big_sum x2 1, k2), r, height r + 1,
                quan r + count (big_sum x2 1, k2))
        else assert false
    else 
      if seek_k1 then
        if c_x1k2 > 0 then
          let new_r = rem_helper x1 x2 true true r in
          Node (l, (k1, k2), new_r, max (height l) (height new_r),
                big_sum (big_sum (quan l) (quan new_r))
                         (count (k1, k2)))
        else if c_x1k1 > 0 then
          Node (l, (k1, big_diff x1 1), Empty, height l,
                big_sum (quan l) (count (k1, big_diff x1 1)))
        else rem_helper x1 x2 true true l
      else
        if c_x2k1 < 0 then
          let new_l = rem_helper x1 x2 false true l in
          Node (new_l, (k1, k2), r, max (height new_l) (height r),
                big_sum (big_sum (quan new_l) (quan r))
                         (count (k1, k2)))
        else if c_x2k2 < 0 then
          Node (Empty, (big_sum x2 1, k2), r, height r,
                big_sum (quan r) (count (big_sum x2 1, k2)))
        else rem_helper x1 x2 false true r


(* remove : int * int -> t -> t                                    *)
(* [remove (x, y) s] zwraca zbiór zawierający te same elementy     *)
(* co [s], z wyjątkiem wszystkich zawartych pomiędzy [x] oraz [y]. *)
(* Zakłada, że [x <= y].                                           *)
let rec remove (x1, x2) = function
  | Empty -> Empty
  | Node (l, (k1, k2), r, _, _) ->
    let lh = height l and rh = height r in
    let c_x1k1 = big_diff x1 k1
    and c_x1k2 = big_diff x1 k2
    and c_x2k1 = big_diff x2 k1
    and c_x2k2 = big_diff x2 k2 in
   
    if c_x1k1 >= 0 && c_x2k2 <= 0 then 
      if c_x1k1 = 0 && c_x2k2 = 0 then 
        merge l r
      else if c_x1k1 = 0 then 
        join l (big_sum x2 1, k2) r
      else if c_x2k2 = 0 then
        join l (k1, big_diff x1 1) r
      else
        let new_r = Node(Empty, (big_sum x2 1, k2), r, height r + 1,
                         big_sum (quan r) (count (big_sum x2 1, k2)))
        in
        Node(l, (k1, big_diff x1 1), new_r, 
             max (height l)(height new_r),
             big_sum (big_sum (quan l) (quan new_r))
                      (count (k1, big_diff x1 1))) 
                      
    else if c_x2k1 < 0 then
      let new_l = remove (x1, x2) l in
      let new_lh = height new_l in
      bal_loop (Node ((remove (x1, x2) new_l), 
                       (k1, k2), r, max new_lh rh + 1,
                       big_sum (big_sum (quan r) (quan new_l)) 
                               (count (k1, k2))))
                               
    else if c_x1k2 > 0 then
      let new_r = remove (x1, x2) r in
      let new_rh = height new_r in
      bal_loop (Node (l, (k1, k2), (remove (x1, x2) new_r),
                      max lh new_rh + 1,
                      big_sum (big_sum (quan l) (quan new_r))
                              (count (k1, k2))))
                              
    else if c_x1k1 = 0 then
      let new_r = rem_helper x1 x2 false false r in
      bal_loop (merge l new_r)

    else if c_x1k1 > 0 then
      let new_r = rem_helper x1 x2 false false r in
      bal_loop (join l (k1, big_diff x1 1) new_r)
      
    else if c_x2k2 = 0 then
      let new_l = rem_helper x1 x2 true false l in
      bal_loop (merge new_l r)
      
    else if c_x2k2 < 0 then
      let new_l = rem_helper x1 x2 true false l in
      bal_loop (join new_l (big_sum x2 1, k2) r)
    
    else
      let new_l = rem_helper x1 x2 true false l in
      let new_r = rem_helper x1 x2 false false r in
      bal_loop (merge new_l new_r)
      
      
(* mem : int -> t -> bool               *)
(* zwraca true jeśli w [t] znajduje się *)
(* element [x] i false wpp              *)
let mem x set =
  let rec loop = function
    | Node (l, (k1, k2), r, _, _) ->
        let ck1 = big_diff x k1
        and ck2 = big_diff x k2 in
        if ck1 < 0 then loop l
        else if ck2 > 0 then loop r 
        else true
    | Empty -> false in
  loop set


(* iter : (int * int -> unit) -> t -> unit    *)
(* aplikuje funkcję f do wszystkich elementów *)
(* zbioru w kolejności rosnącej               *)
let iter f set =
  let rec loop = function
    | Empty -> ()
    | Node (l, k, r, _, _) -> loop l; f k; loop r in
  loop set


(* fold : (int * int -> 'a -> 'a) -> t -> 'a -> 'a                 *)
(* [fold f s a] zwraca [(f xN ... (f x2 (f x1 a))...)], gdzie      *)
(* x1 ... xN są ciągłymi przedziałami w [s], w kolejności rosnącej *)
let fold f set acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, k, r, _, _) ->
          loop (f k (loop acc l)) r in
  loop acc set


(* elements : t -> (int * int) list                 *)
(* zwraca posortowaną w kolejności rosnącej listę   *)
(* wszystkich ciągłych przedziałów w danym zbiorze. *)
let elements set = 
  let rec loop acc = function
      Empty -> acc
    | Node(l, k, r, _, _) -> loop (k :: loop acc r) l in
  loop [] set


(* below : int -> t -> int                                   *)
(* [below n s] zwraca liczbę elementów [s] które są mniejsze *)
(* lub równe [n]. Jeśli takich elementów jest więcej         *)
(* niż max_int, wówczas wynikiem jest max_int.               *)
let rec below x = function
  | Empty -> 0
  | Node (l, (k1, k2), r, _, _) ->
      if x < k1 then
        below x l
      else if x > k2 then
        big_sum (big_sum (quan l) (count (k1, k2))) (below x r)
      else
        big_sum (quan l) (big_sum (big_diff x k1) 1)




(* Testy - ze wspólnej puli *)
(*
let good = ref 0 and bad = ref 0

let check nr warunek wartosc =
  if warunek = wartosc then
    begin
      (* Printf.printf "OK - TEST nr %d \n" nr; *)
      incr good
    end
  else
    begin
      Printf.printf "Fail: %d\n" nr;
      assert (false);
    end;;

open ISet;;

let liczba a = List.length (elements a)

(* Testy na add i remove *)

let a = empty
let a = add (17, 20) a
let a = add (5, 8) a
let a = add (1, 2) a
let a = add (10, 12) a
let a = add (28, 35) a
let a = add (22, 23) a
let a = add (40, 43) a
let a = add (37, 37) a;;

check 1 (is_empty a) false;;
check 2 (mem 29 a) true;;
check 3 (mem 21 a) false;;
check 4 (mem 38 a) false;;
check 5 (mem 37 a) true;;
check 6 (below 8 a = below 9 a) true;;
check 7 (below 29 a) 17;;
check 8 (liczba a) 8;;

let a = add (37, 42) a;;

check 9 (liczba a) 7;;
check 10 (mem 37 a) true;;
check 11 (mem 38 a) true;;
check 12 (mem 39 a) true;;
check 13 (mem 40 a) true;;
check 14 (mem 41 a) true;;
check 15 (mem 42 a) true;;
check 16 (mem 44 a) false;;
check 17 (below 38 a = below 39 a) false;;

let tmp = remove (8, 22) a;;
let tmp = add (8, 22) tmp;;

check 18 (elements tmp = elements a) false;;

(* Testy na split *)

let (l, exists, p) = split 9 a;;

check 19 exists false;;
check 20 (liczba l) 2;;
check 21 (liczba p) 5;;
check 22 (mem 10 l) false;;
check 23 (mem 9 l) false;;
check 24 (mem 8 l) true;;
check 25 (mem 1 l) true;;
check 26 (mem 9 p) false;;
check 27 (mem 10 p) true;;
check 28 (mem 17 p) true;;
check 29 (mem 29 p) true;;
check 30 (mem 24 p) false;;
check 31 (mem 38 p) true;;
check 32 ((elements l @ elements p) = elements a) true;;

let (l, exists, p) = split 21 a;;

check 33 exists false;;
check 34 ((elements l @ elements p) = elements a) true;;

let (l, exists, p) = split 15 a;;
check 35 exists false;;
check 36 ((elements l @ elements p) = elements a) true;;


let b = empty
let b = add (5, 10) b
let b = add (40, 50) b
let b = add (20, 25) b
let b = add (12, 14) b
let b = add (17, 18) b
let b = add (52, 60) b
let b = add (62, 80) b
let b = add (83, 100) b;;

check 37 (mem 41 b) true;;
check 38 (mem 11 b) false;;

let d = empty;;
let (l, ex, p) = split 0 d;;

check 39 (is_empty l) true;;
check 40 (is_empty p) true;;

let d = add (17, 30) d;;
let d = add (1, 3) d;;
let d = add (10, 10) d;;
let d = remove (11, 11) d;;
let d = add (12, 14) d;;
let d = add (32, 35) d;;
let d = add (38, 40) d;;

check 41 (below 36 d = below 37 d) true;;

let d = add (36, 37) d;;

check 42 (below 36 d = below 37 d) false;;

let d = remove (37, 37) d;;
check 43 (below 36 d = below 37 d) true;;

let d = remove (20, 21) d;;

check 44 (elements d) [(1, 3); (10, 10); (12, 14); (17, 19); (22, 30); (32, 36); (38, 40)];;

let (l, ex, p) = split 15 d;;
check 144 (elements l) [(1, 3); (10, 10); (12, 14)];;
check 145 (elements p) [(17, 19); (22, 30); (32, 36); (38, 40)];;

check 45 ((elements l @ elements p) = elements d) true;;
check 46 (liczba l, liczba p) (3, 4);;

check 47 (mem 13 l) true;;
check 48 (mem 14 l) true;;
check 49 ex false;;

let (l, ex, p) = split 25 d;;

check 50 ex true;;
check 51 (elements l) [(1, 3); (10, 10); (12, 14); (17, 19); (22, 24)];;
check 52 (elements p) [(26, 30); (32, 36); (38, 40)];;
*)
