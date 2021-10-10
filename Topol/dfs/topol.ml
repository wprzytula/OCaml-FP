(* Sortowanie topologiczne  *)
(* Autor: Wojciech Przytuła *)
(* Reviewer: Jan Wawszczak  *)

(*
 * PSet - Polymorphic sets
 * Copyright (C) 1996-2003 Xavier Leroy, Nicolas Cannasse, Markus Mottl
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
module PSet = struct
  type 'k set =
    | Empty
    | Node of 'k set * 'k * 'k set * int

  type 'k t =
    {
      cmp : 'k -> 'k -> int;
      set : 'k set;
    }

  let height = function
    | Node (_, _, _, h) -> h
    | Empty -> 0

  let make l k r = Node (l, k, r, max (height l) (height r) + 1)

  let bal l k r =
    let hl = height l in
    let hr = height r in
    if hl > hr + 2 then
      match l with
      | Node (ll, lk, lr, _) ->
          if height ll >= height lr then make ll lk (make lr k r)
          else
            (match lr with
            | Node (lrl, lrk, lrr, _) ->
                make (make ll lk lrl) lrk (make lrr k r)
            | Empty -> assert false)
      | Empty -> assert false
    else if hr > hl + 2 then
      match r with
      | Node (rl, rk, rr, _) ->
          if height rr >= height rl then make (make l k rl) rk rr
          else
            (match rl with
            | Node (rll, rlk, rlr, _) ->
                make (make l k rll) rlk (make rlr rk rr)
            | Empty -> assert false)
      | Empty -> assert false
    else Node (l, k, r, max hl hr + 1)

  let rec min_elt = function
    | Node (Empty, k, _, _) -> k
    | Node (l, _, _, _) -> min_elt l
    | Empty -> raise Not_found

  let rec remove_min_elt = function
    | Node (Empty, _, r, _) -> r
    | Node (l, k, r, _) -> bal (remove_min_elt l) k r
    | Empty -> invalid_arg "PSet.remove_min_elt"

  let merge t1 t2 =
    match t1, t2 with
    | Empty, _ -> t2
    | _, Empty -> t1
    | _ ->
        let k = min_elt t2 in
        bal t1 k (remove_min_elt t2)

  let create cmp = { cmp = cmp; set = Empty }
  let empty = { cmp = compare; set = Empty }

  let is_empty x = 
    x.set = Empty

  let rec add_one cmp x = function
    | Node (l, k, r, h) ->
        let c = cmp x k in
        if c = 0 then Node (l, x, r, h)
        else if c < 0 then
          let nl = add_one cmp x l in
          bal nl k r
        else
          let nr = add_one cmp x r in
          bal l k nr
    | Empty -> Node (Empty, x, Empty, 1)

  let add x { cmp = cmp; set = set } =
    { cmp = cmp; set = add_one cmp x set }

  let rec join cmp l v r =
    match (l, r) with
      (Empty, _) -> add_one cmp v r
    | (_, Empty) -> add_one cmp v l
    | (Node(ll, lv, lr, lh), Node(rl, rv, rr, rh)) ->
        if lh > rh + 2 then bal ll lv (join cmp lr v r) else
        if rh > lh + 2 then bal (join cmp l v rl) rv rr else
        make l v r

  let split x { cmp = cmp; set = set } =
    let rec loop x = function
        Empty ->
          (Empty, false, Empty)
      | Node (l, v, r, _) ->
          let c = cmp x v in
          if c = 0 then (l, true, r)
          else if c < 0 then
            let (ll, pres, rl) = loop x l in (ll, pres, join cmp rl v r)
          else
            let (lr, pres, rr) = loop x r in (join cmp l v lr, pres, rr)
    in
    let setl, pres, setr = loop x set in
    { cmp = cmp; set = setl }, pres, { cmp = cmp; set = setr }

  let remove x { cmp = cmp; set = set } =
    let rec loop = function
      | Node (l, k, r, _) ->
          let c = cmp x k in
          if c = 0 then merge l r else
          if c < 0 then bal (loop l) k r else bal l k (loop r)
      | Empty -> Empty in
    { cmp = cmp; set = loop set }

  let mem x { cmp = cmp; set = set } =
    let rec loop = function
      | Node (l, k, r, _) ->
          let c = cmp x k in
          c = 0 || loop (if c < 0 then l else r)
      | Empty -> false in
    loop set

  let exists = mem

  let iter f { set = set } =
    let rec loop = function
      | Empty -> ()
      | Node (l, k, r, _) -> loop l; f k; loop r in
    loop set

  let fold f { cmp = cmp; set = set } acc =
    let rec loop acc = function
      | Empty -> acc
      | Node (l, k, r, _) ->
            loop (f k (loop acc l)) r in
    loop acc set

  let elements { set = set } = 
    let rec loop acc = function
        Empty -> acc
      | Node(l, k, r, _) -> loop (k :: loop acc r) l in
    loop [] set
  end


(* Sortowanie topologiczne *)


(** wyjatek rzucany przez [topol] gdy zaleznosci sa cykliczne *)
exception Cykliczne;;


(* into_map : ('a * 'a list) list ->
    ('a * 'a t) map ref -> ('a * 'a t) map *)
(* przyjmuje graf w postaci listy par wierzchołek - lista jego krawędzi
   i zwraca mapę wierzchołków na zbiory ich krawędzi. Jeśli wierzchołek
   nie zostanie explicite opisany (tzn. nie wychodzi z niego żadna krawędź
   i nie występuje jako pierwszy element żadnej pary), to zostaje również
   dodany do mapy z pustym zbiorem. *)
let rec make_from_edge_map acc = function
  | [] -> !acc
  | (key, values) :: tail -> 
    let list_to_set set value =
      if not (PMap.mem value !acc) then
        acc := PMap.add value PSet.empty !acc;
      PSet.add value set in
    if PMap.mem key !acc then
      let previous = PMap.find key !acc in
      let new_values = List.fold_left list_to_set previous values in
      acc := PMap.add key new_values !acc;
      make_from_edge_map acc tail
    else
      let new_values = List.fold_left list_to_set PSet.empty values in
      acc := PMap.add key new_values !acc;
      make_from_edge_map acc tail 


(* topol : ('a * 'a list) list -> 'a list                             *)
(* Dla danej listy [(a_1,[a_11;...;a_1n]); ...; (a_m,[a_m1;...;a_mk])] 
   zwraca liste, na ktorej kazdy z elementow a_i oraz a_ij wystepuje
   dokladnie raz i ktora jest uporzadkowana w taki sposob, ze kazdy
   element a_i jest przed kazdym z elementow a_i1 ... a_il            *)
let topol = function
  | [] -> []
  | lst ->
    let from_edge_map = make_from_edge_map (ref PMap.empty) lst in
    let result = ref [] in
    let temp_marked = ref PSet.empty
    and perma_marked = ref PSet.empty in
    
    let rec dfs vertex =
      if PSet.mem vertex !perma_marked then () else
      if PSet.mem vertex !temp_marked then raise Cykliczne else
      begin
        temp_marked := PSet.add vertex !temp_marked;
        let edges = PMap.find vertex from_edge_map in
        PSet.iter dfs edges;
        temp_marked := PSet.remove vertex !temp_marked;
        perma_marked := PSet.add vertex !perma_marked;
        result := vertex :: !result
      end
      
    in PMap.iter (fun vertex _ -> 
                    if not (PSet.mem vertex !perma_marked) then dfs vertex)
                 from_edge_map;
    !result



(* Testy - ze wspólnej puli  *)

(*
exception WA;;

let debug = false;;

(* True if the given order is a correct topological order, *)
(* false otherwise. Checks all edges.                      *)
let test graph order =
  let hashtbl = Hashtbl.create (List.length order)
  in
  List.iteri (fun i x -> Hashtbl.add hashtbl x i) order;
  let check_one (v, l) =
    List.iter (fun u ->
      if (Hashtbl.find hashtbl v) > (Hashtbl.find hashtbl u)
      then raise WA;) l
  in
  try (List.iter check_one graph; true)
  with WA -> false

(* Tests if Topol raises Cykliczne for the given graph *)
let test_cyclic g =
  try let _ = topol g in false
  with Cykliczne -> true

;;
      
if debug then print_endline "Acyclic correctness tests...";;
      
let g = [
  ("1", ["2"; "3"]);
  ("3", ["2"]);
  ("4", ["3"; "2"])
];;

assert(test g (topol g));;

let g = [
  ("first", ["second"; "fourth"; "eighth"]);
  ("second", ["fourth"; "eighth"]);
  ("third", ["fourth"; "fifth"; "sixth"]);
  ("fourth", ["eighth"]);
  ("fifth", ["sixth"; "seventh"]);
  ("sixth", ["eighth"; "first"]);
  ("seventh", ["eighth"]);
];;

assert(test g (topol g));;

let g = [
  (1, [2; 3]);
  (2, [4]);
  (3, [4]);
  (4, [5; 6]);
  (5, [7]);
  (6, [7]);
];;

assert(test g (topol g));;

let g = [
  (1, [7; 2]);
  (3, [4; 2; 1; 7; 5]);
  (4, [2; 7; 1]);
  (5, [7; 4; 1; 2]);
  (6, [1; 3; 2; 5; 4; 7]);
  (7, [2])
];;

assert(test g (topol g));;

let g = [
  (1, [2; 4; 8]);
  (2, [16; 32]);
  (4, [64; 128]);
  (8, [256; 512]);
  (16, [1024]);
  (32, [2048]);
  (64, [4096]);
  (128, [8192]);
  (256, [16384]);
  (512, [32768]);
];;

assert(test g (topol g));;

let g = [
  ("Lorem", ["sit"]);
  ("ipsum", ["sit"; "amet"]);
  ("dolor", ["amet"; "elit"]);
  ("sit", ["consectetur"; "adipiscing"; "elit"]);
];;

assert(test g (topol g));;

let g = [];;

assert(test g (topol g));;

let g = [
  ("through", ["the"; "gates"; "of"; "hell"]);
  ("hell", ["as"; "we"; "make"; "our"; "way"; "to"; "heaven"]);
  ("PRIMO", ["VICTORIA"]);
];;

assert(test g (topol g));;

let g = [
  ("one", ["three"]);
  ("one", ["two"]);
  ("two", []);
  ("two", []);
  ("two", ["three"]);
];;

assert(test g (topol g));;

if debug then print_endline "OK";;

if debug then print_endline "Cyclic correctness tests...";;

let g = [
  (10.001, [10.002]);
  (10.002, [10.001])
];;

assert(test_cyclic g);;

let g = [
  (1, [7; 2; 3]);
  (3, [4; 2; 1; 7; 5]);
  (4, [2; 7; 1]);
  (5, [7; 4; 1; 2]);
  (6, [1; 3; 2; 5; 4; 7]);
  (7, [2])
];;

assert(test_cyclic g);;

let g = [
  (1, [2]);
  (2, [3]);
  (3, [4; 5; 3]);
];;

assert(test_cyclic g);;

let g = [
  ("pole", ["pole"; "lyse"; "pole"])
];;

assert(test_cyclic g);;

let g = [
  ("tu", ["tudu"]);
  ("tudu", ["tudu"; "tudu"; "tudu"])
];;

assert(test_cyclic g);;

if debug then print_endline "OK";;

if debug then print_endline "Marcin Michorzewski's acyclic correctness tests...";;

let g = [
  (11, [12]);
  (12, [13]);
  (7, [8]);
  (8, [9]);
  (1, [2]);
  (13, [6]);
  (3, [4]);
  (5, [6]);
  (6, [7]);
  (10, [11])
];;

assert(test g (topol g));;

let g = [
  (1, [2]);
  (3, [4]);
  (4, [1]);
  (5, [6]);
  (6, [3])
];;

assert(test g (topol g));;

let g = [
  (1, [2; 3; 4]);
  (3, [7; 8]);
  (4, [9; 10]);
  (10, [15; 16]);
  (2, [5; 6]);
  (13, [4; 10]);
  (11, [12]);
  (12, [13; 14])
];;

assert(test g (topol g));;

let g = [
  (1, [2; 3; 4]);
  (3, [7; 8]);
  (4, [9; 10]);
  (10, [15; 16]);
  (2, [5; 6]);
  (13, [4; 10]);
  (11, [12]);
  (12, [13; 14]);
  (15, [16; 8])
];;

assert(test g (topol g));;

let g = [
  (1, [2; 3; 4]);
  (3, [7; 8]);
  (4, [9; 10]);
  (10, [15; 16]);
  (2, [5; 6]);
  (13, [4; 10]);
  (11, [12]);
  (12, [13; 14]);
  (15, [16; 8]);
  (8, [14])
];;

assert(test g (topol g));;

let g = [
  (1, [2]);
  (2, []);
  (3, [2])
];;

assert(test g (topol g));;

let g = [
  ('a', ['e']);
  ('b', ['a'; 'c']);
  ('c', ['a']);
  ('e', [])
];;

assert(test g (topol g));;

if debug then print_endline "OK";;

if debug then print_endline "Marcin Michorzewski's cyclic correctness tests...";;

let g = [
  (3, [4]);
  (5, [6]);
  (6, [7]);
  (10, [11]);
  (11, [12]);
  (12, [13]);
  (7, [8]);
  (9, [13]);
  (8, [9]);
  (1, [2]);
  (13, [6])
];;

assert(test_cyclic g);;

let g = [
  ("Polska", ["Niemcy"]);
  ("Niemcy", ["Polska"])
];;

assert(test_cyclic g);;

let g = [
  (1, [2]);
  (3, [4]);
  (4, [1]);
  (5, [6]);
  (6, [3]);
  (2, [5])
];;

assert(test_cyclic g);;

let g = [
  (1, [2]);
  (3, [4]);
  (4, [1]);
  (5, [6]);
  (6, [3]);
  (1, [5]);
];;

assert(test_cyclic g);;

let g = [
  (1, [2]);
  (3, [4]);
  (4, [1]);
  (5, [6]);
  (6, [3]);
  (2, [6])
];;

assert(test_cyclic g);;

let g = [
  (1, [2]);
  (3, [4]);
  (4, [1]);
  (5, [6]);
  (6, [3]);
  (1, [6])
];;

assert(test_cyclic g);;

let g = [
  (1, [2]);
  (2, [3]);
  (3, [1])
];;

assert(test_cyclic g);;

let g = [
  (1, [2; 3; 4]);
  (3, [7; 8]);
  (4, [9; 10]);
  (10, [15; 16]);
  (2, [5; 6]);
  (13, [4; 10]);
  (11, [12]);
  (12, [13; 14]);
  (15, [16; 8]);
  (8, [12])
];;

assert(test_cyclic g);;
*)
