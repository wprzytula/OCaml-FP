(* ORIGAMI *)
(* Autor: Wojciech Przytuła *)
(* Reviewer: Mateusz Ładysz *)


(* Punkt na płaszczyźnie *)
type point = float * float


(* Poskładana kartka: ile razy kartkę     *)
(* przebije szpilka wbita w danym punkcie *)
type kartka = point -> int


(* Dopuszczalny błąd obliczeń na floatach *)
let epsilon = 1e-8


(* eps_rowne : float -> float -> bool                 *)
(* zwraca true jeśli liczby są równe z uwzględnieniem *)
(* błędów obliczeń na floatach, lub false wpp         *)
let eps_rowne a b =
  a +. epsilon > b && b +. epsilon > a


(* odbicie : point -> point -> point -> point                       *)
(* przyjmuje dwa punkty wyznaczające prostą oraz trzeci punkt,      *)
(* a następnie zwraca jego odbicie symetryczne względem tej prostej *)
let odbicie (x1, y1) (x2, y2) (x, y) =
  let a = x1 -. x2
  and b = y1 -. y2 in
  let c = a *. x +. b *. y
  and d = a *. y2 -. b *. x2 in
  let m = a ** 2. +. b ** 2. in
  let pre_x = (a *. c -. b *. d) /. m
  and pre_y = (a *. d +. b *. c) /. m in
  (2. *. pre_x -. x, 2. *. pre_y -. y)
  

(* odleglosc_punktow : point -> point -> float           *)
(* przyjmuje dwa punkty i zwraca ich odległość od siebie *)
let odleglosc_punktow (x1, y1) (x2, y2) =
  sqrt ((x1 -. x2) ** 2. +. (y1 -. y2) ** 2.)


(* strona_prostej : point -> point -> point -> int      *)
(* przyjmuje dwa punkty wyznaczające prostą i punkt p   *)
(* oraz zwraca 0 jeśli [p] leży na niej, < 0 jeśli leży *)
(* po jej prawej stronie i > 0 jeśli leży po jej lewej  *) 
let strona_prostej (x1, y1) (x2, y2) (x, y) =
  (* wektor u: p1 -> p2 *)
  let (ux, uy) = (x2 -. x1, y2 -. y1) in
  (* wektor v : p1 -> p *)
  let (vx, vy) = (x -. x1, y -. y1) in
  (* iloczyn wektorowy wektorów u x v *)
  ux *. vy -. uy *. vx


(* prostokat : point -> point -> kartka                                *)
(* [prostokat p1 p2] zwraca kartkę, reprezentującą domknięty           *)
(* prostokąt o bokach równoległych do osi układu współrzędnych i lewym *)
(* dolnym rogu [p1] a prawym górnym [p2]. Punkt [p1] musi więc być     *)
(* nieostro na lewo i w dół od punktu [p2]. Gdy w kartkę tę wbije się  *)
(* szpilkę wewnątrz (lub na krawędziach) prostokąta, kartka zostanie   *)
(* przebita 1 raz, w pozostałych przypadkach 0 razy                    *)
let prostokat (lim_x_left, lim_y_bot) (lim_x_right, lim_y_top) =
  let prostokatna (x, y) =
    if x < lim_x_left || x > lim_x_right
       || y < lim_y_bot || y > lim_y_top
    then 0 else 1
  in
  prostokatna


(* [kolko p0 r] zwraca kartkę, reprezentującą kółko domknięte *)
(* o środku w punkcie [p0] i promieniu [r]                    *)
(* kolko : point -> float -> kartka                          *)
let kolko p0 r =
  let okragla p =
    if odleglosc_punktow p0 p > r +. epsilon then 0 else 1
  in
  okragla


(* zloz : point -> point -> kartka -> kartka                             *)
(* [zloz p1 p2 k] składa kartkę [k] wzdłuż prostej przechodzącej         *)
(* przez punkty [p1] i [p2] (muszą to być różne punkty). Papier jest     *)
(* składany w ten sposób, że z prawej strony prostej (patrząc w kierunku *)
(* od [p1] do [p2]) jest przekładany na lewą. Wynikiem funkcji jest      *)
(* złożona kartka. Jej przebicie po prawej stronie prostej powinno więc  *)
(* zwrócić 0. Przebicie dokładnie na prostej powinno zwrócić tyle samo,  *)
(* co przebicie kartki przed złożeniem. Po stronie lewej - tyle co przed *)
(* złożeniem plus przebicie rozłożonej kartki w punkcie, który nałożył   *)
(* się na punkt przebicia. *)
let zloz p1 p2 k =
  let zlozona ((x, y) as p) =
    let strona p = strona_prostej p1 p2 p in
    if eps_rowne (strona p) 0. then k p
    else if strona p < 0. then 0
    else
      let odbity = odbicie p1 p2 p in
      k p + k odbity
  in zlozona


(* skladaj : (point * point) list -> kartka -> kartka     *)
(* [skladaj [(p1_1,p2_1);...;(p1_n,p2_n)] k =             *)
(* zloz p1_n p2_n (zloz ... (zloz p1_1 p2_1 k)...)]       *)
(* czyli wynikiem jest złożenie kartki [k] kolejno wzdłuż *)
(* wszystkich prostych z listy                            *)
let skladaj lista_punktow k =
  List.fold_left (fun robocza_kartka (p1, p2) ->
    zloz p1 p2 robocza_kartka)
   k lista_punktow



(* Testy ze wspólnej puli *)
(*
let zle = ref 0
let test n b =
  if not b then begin
    Printf.printf "Zly wynik testu %d!!\n" n;
    incr zle
  end

let epsilon = 0.0001

let (=.) x y = (x-.epsilon <= y) && (y <= x+.epsilon)


(*Printf.printf "==== Testy obowiazkowe...\n";;*)

let a = (1., 1.);;
let b = (10., 10.);;
let c = (5., 5.);;
let d = (5., 1.);;
let e = (5., 10.);;
let x = (5., 11.);;
let y = (0., 10.);;

let f = prostokat a b;;

test 1 (f a = 1);;
test 2 (f b = 1);;
test 3 (f c = 1);;
test 4 (f d = 1);;
test 5 (f e = 1);;
test 6 (f x = 0);;
test 7 (f y = 0);;

let g = zloz d c f;;

test 8  (g a = 2);;
test 9  (g b = 0);;
test 10 (g c = 1);;
test 11 (g d = 1);;
test 12 (g e = 1);;
test 13 (g x = 0);;
test 14 (g y = 1);;

let h = zloz (1., 3.) (6., 3.) g;;

test 15 (h a = 0);;
test 16 (h b = 0);;
test 17 (h c = 2);;
test 18 (h d = 0);;
test 19 (h e = 1);;
test 20 (h x = 0);;
test 21 (h y = 1);;
test 22 (h (1., 5.) = 4);;
test 23 (h (0., 4.) = 2);;
test 24 (h (3., 4.) = 4);;
test 25 (h (5., 3.) = 1);;


(* .... i pewnie sporo innych przykladow ... *)

(*Printf.printf "==== Moje przyklady...\n";;*)

let pom = [(d, c);((1., 3.),(6., 3.))];;
let h = skladaj pom f;;

test 35 (h a = 0);;
test 36 (h b = 0);;
test 37 (h c = 2);;
test 38 (h d = 0);;
test 39 (h e = 1);;
test 40 (h x = 0);;
test 41 (h y = 1);;
test 42 (h (1., 5.) = 4);;
test 43 (h (0., 4.) = 2);;
test 44 (h (3., 4.) = 4);;
test 45 (h (5., 3.) = 1);;

let a = (1., 1.);;
let b = (5., 2.);;
let c = (6., 5.);;
let d = (9., 5.);;
let e = (3., 4.);;

let f = prostokat (0., 0.) (9., 5.);;

test 46 (f a = 1);;
test 47 (f b = 1);;
test 48 (f c = 1);;
test 49 (f d = 1);;
test 50 (f e = 1);;

let f = skladaj [((3.,10.),(3.,0.));((6.,1.),(6.,4.))] f;;

test 51 (f a = 0);;
test 52 (f b = 3);;
test 53 (f c = 2);;
test 54 (f d = 0);;
test 55 (f e = 2);;

let g = kolko (0., 0.) 6.;;

test 56 (g (0., 0.) = 1);;
test 57 (g (6., 0.) = 1);;
test 58 (g (0., 6.1) = 0);;
test 59 (g (3., 5.196) = 1);;
test 60 (g (-3., 5.2) = 0);;

let g = zloz (5.,0.) (10.,0.) g;;

test 61 (g (0., 0.) = 1);;
test 62 (g (6., 0.) = 1);;
test 63 (g (0., 6.1) = 0);;
test 64 (g (3., 5.196) = 2);;
test 65 (g (-3., 5.2) = 0);;

(*Printf.printf "==== Pieklo niebo...\n";;*)

let x = prostokat (-16., -16.) (16., 16.);;

let a = (0., -16.);;
let b = (0., 16.);;
let c = (-16., 0.);;
let d = (16., 0.);;

let x = skladaj [(a,d);(d,b);(b,c);(c,a)] x;;

test 66 (x (0., 0.) = 5);;
test 67 (x (6., 0.) = 3);;
test 68 (x a = 1);;
test 69 (x (-16., -16.) = 0);;
test 70 (x (-8., 8.) = 1);;

let a = (-8., -8.);;
let b = (8., 8.);;
let c = (-8., 8.);;
let d = (8., -8.);;

let x = skladaj [(a,d);(d,b);(b,c);(c,a)] x;;

test 66 (x (0., 0.) = 9);;
test 67 (x (6., 0.) = 6);;
test 68 (x a = 1);;
test 69 (x (-16., -16.) = 0);;
test 70 (x (0., 8.) = 3);;

let _ = 
  if !zle <> 0 then  
    Printf.printf "\nBlednych testow: %d...\n" !zle
;;
*)
