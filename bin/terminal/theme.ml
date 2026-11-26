(* The terminal's colours: the identity's, for the dark or light
   ground the terminal says it has. *)

open Look

type palette = {
  ground : colour;
  ink : colour;
  muted : colour;
  faint : colour;
  punct : colour;
  comment : colour;
  thread : colour;
  keyword : colour;
  str : colour;
  number : colour;
  ty : colour;
  error : colour;
  strip : colour; (* under the input *)
  selected : colour; (* under a menu's choice *)
}

let mix (r, g, b) (r', g', b') t =
  let m x y = x + int_of_float (Float.round (float (y - x) *. t)) in
  (m r r', m g g', m b b')

(* The input's strip and a menu's choice are mixed from the ground itself, so
   they suit any profile. *)
let on ground p = { p with ground; strip = mix ground p.ink 0.06; selected = mix ground p.thread 0.15 }

let walnut =
  on (14, 13, 11)
    {
      ground = (0, 0, 0);
      ink = (221, 218, 212);
      muted = (159, 154, 147);
      faint = (113, 105, 92);
      punct = (122, 114, 102);
      comment = (125, 118, 108);
      thread = (216, 166, 79);
      keyword = (151, 182, 145);
      str = (208, 155, 139);
      number = (190, 170, 207);
      ty = (141, 176, 173);
      error = (226, 111, 124);
      strip = (0, 0, 0);
      selected = (0, 0, 0);
    }

let linen =
  on (238, 232, 221)
    {
      walnut with
      ink = (46, 40, 31);
      muted = (100, 94, 84);
      faint = (133, 125, 113);
      punct = (140, 132, 120);
      comment = (122, 114, 102);
      thread = (117, 91, 31);
      keyword = (64, 95, 58);
      str = (143, 72, 50);
      number = (109, 77, 137);
      ty = (53, 90, 87);
      error = (174, 41, 56);
    }

let current = ref walnut

(* A terminal that doesn't say gets the dark colours. *)
let choose = function
  | None -> ()
  | Some ((r, g, b) as ground) ->
      let light = (2126 * r) + (7152 * g) + (722 * b) > 1_275_000 in
      current := on ground (if light then linen else walnut)

(* A colour sunk toward the ground: the other shade of a long number's digits. *)
let dim c = mix c !current.ground 0.35

let ink () = !current.ink
let muted () = !current.muted
let faint () = !current.faint
let thread () = !current.thread
let error () = !current.error
let strip () = !current.strip
let selected () = !current.selected

(* Some terminals show bold text in the default colour in another colour, so
   bold text is always given one. *)
let bold c = { (fg c) with bold = true }

let cursor style =
  if !mode = No_colour then { style with reverse = true }
  else { style with bg = Some (thread ()); fg = Some !current.ground }

let style_of : Syntax.cls -> style = function
  | Space -> plain
  | Name -> fg !current.ink
  | Bracket -> fg !current.punct
  | Str -> fg !current.str
  | Comment -> { (fg !current.comment) with italic = true }
  | Keyword -> fg !current.keyword
  | Number -> fg !current.number
  | Form -> fg !current.thread

(* [src] coloured; [marks] change the style of byte ranges. *)
let code ?(marks = []) src =
  let cls = Syntax.classify src in
  let rec go i acc =
    if i >= String.length src then List.rev acc
    else
      let j = next_char src i in
      let style =
        List.fold_left
          (fun st (a, b, change) -> if a <= i && i < b then change st else st)
          (style_of cls.(i)) marks
      in
      go j ({ ch = String.sub src i (j - i); style } :: acc)
  in
  go 0 []

let types s =
  List.map (fun c -> if c.style.fg = Some !current.punct then c else { c with style = fg !current.ty }) (code s)
