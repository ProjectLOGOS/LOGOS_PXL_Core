(** OCaml Bridge Layer for Verified Modal Logic Evaluation **)

open List
open String

(** Core types from extracted Coq code **)
type modal_prop =
  | MProp of string
  | MBot
  | MNeg of modal_prop
  | MConj of modal_prop * modal_prop
  | MDisj of modal_prop * modal_prop
  | MImpl of modal_prop * modal_prop
  | MBox of modal_prop
  | MDia of modal_prop

type iel_operator =
  | IIdentity of string
  | IExperience of string
  | IUnification of iel_operator * iel_operator

type iel_modal_prop =
  | IELBase of modal_prop
  | IELOp of iel_operator * iel_modal_prop

type modal_context = {
  mc_world : string;
  mc_accessible : string list;
  mc_valuation : string -> bool;
}

(** ========== JSON Serialization ========== **)

let rec modal_prop_to_json = function
  | MProp s -> `Assoc [("type", `String "MProp"); ("value", `String s)]
  | MBot -> `Assoc [("type", `String "MBot")]
  | MNeg p -> `Assoc [("type", `String "MNeg"); ("operand", modal_prop_to_json p)]
  | MConj (p, q) -> `Assoc [("type", `String "MConj");
                           ("left", modal_prop_to_json p);
                           ("right", modal_prop_to_json q)]
  | MDisj (p, q) -> `Assoc [("type", `String "MDisj");
                           ("left", modal_prop_to_json p);
                           ("right", modal_prop_to_json q)]
  | MImpl (p, q) -> `Assoc [("type", `String "MImpl");
                           ("antecedent", modal_prop_to_json p);
                           ("consequent", modal_prop_to_json q)]
  | MBox p -> `Assoc [("type", `String "MBox"); ("operand", modal_prop_to_json p)]
  | MDia p -> `Assoc [("type", `String "MDia"); ("operand", modal_prop_to_json p)]

let rec iel_operator_to_json = function
  | IIdentity s -> `Assoc [("type", `String "IIdentity"); ("value", `String s)]
  | IExperience s -> `Assoc [("type", `String "IExperience"); ("value", `String s)]
  | IUnification (op1, op2) -> `Assoc [("type", `String "IUnification");
                                      ("left", iel_operator_to_json op1);
                                      ("right", iel_operator_to_json op2)]

let rec iel_modal_prop_to_json = function
  | IELBase mp -> `Assoc [("type", `String "IELBase"); ("modal_prop", modal_prop_to_json mp)]
  | IELOp (op, mp) -> `Assoc [("type", `String "IELOp");
                             ("operator", iel_operator_to_json op);
                             ("modal_prop", iel_modal_prop_to_json mp)]

(** ========== String Parsing ========== **)

(** Simple recursive descent parser for modal propositions **)
exception ParseError of string

let tokenize input =
  let len = String.length input in
  let rec aux acc i =
    if i >= len then List.rev acc
    else match input.[i] with
      | ' ' | '\t' | '\n' -> aux acc (i + 1)
      | '(' -> aux ("(" :: acc) (i + 1)
      | ')' -> aux (")" :: acc) (i + 1)
      | '&' when i + 1 < len && input.[i + 1] = '&' -> aux ("&&" :: acc) (i + 2)
      | '|' when i + 1 < len && input.[i + 1] = '|' -> aux ("||" :: acc) (i + 2)
      | '-' when i + 1 < len && input.[i + 1] = '>' -> aux ("->" :: acc) (i + 2)
      | '~' -> aux ("~" :: acc) (i + 1)
      | '[' when i + 1 < len && input.[i + 1] = ']' -> aux ("[]" :: acc) (i + 2)
      | '<' when i + 1 < len && input.[i + 1] = '>' -> aux ("<>" :: acc) (i + 2)
      | 'a'..'z' | 'A'..'Z' | '_' ->
          let j = ref (i + 1) in
          while !j < len && (match input.[!j] with
                           | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> true
                           | _ -> false) do
            incr j
          done;
          let token = String.sub input i (!j - i) in
          aux (token :: acc) !j
      | c -> raise (ParseError ("Unexpected character: " ^ String.make 1 c))
  in
  aux [] 0

let rec parse_modal tokens =
  let rec parse_atom = function
    | [] -> raise (ParseError "Unexpected end of input")
    | "(" :: rest ->
        let (prop, rest') = parse_modal rest in
        (match rest' with
         | ")" :: rest'' -> (prop, rest'')
         | _ -> raise (ParseError "Missing closing parenthesis"))
    | "~" :: rest ->
        let (prop, rest') = parse_atom rest in
        (MNeg prop, rest')
    | "[]" :: rest ->
        let (prop, rest') = parse_atom rest in
        (MBox prop, rest')
    | "<>" :: rest ->
        let (prop, rest') = parse_atom rest in
        (MDia prop, rest')
    | "bot" :: rest -> (MBot, rest)
    | token :: rest when String.length token > 0 &&
                        (match token.[0] with 'a'..'z' | 'A'..'Z' | '_' -> true | _ -> false) ->
        (MProp token, rest)
    | token :: _ -> raise (ParseError ("Unexpected token: " ^ token))
  in

  let rec parse_impl left = function
    | "->" :: rest ->
        let (right, rest') = parse_modal rest in
        (MImpl (left, right), rest')
    | rest -> (left, rest)
  in

  let rec parse_disj left = function
    | "||" :: rest ->
        let (right, rest') = parse_conj rest in
        parse_disj (MDisj (left, right)) rest'
    | rest -> parse_impl left rest

  and parse_conj left = function
    | "&&" :: rest ->
        let (right, rest') = parse_atom rest in
        parse_conj (MConj (left, right)) rest'
    | rest -> parse_disj left rest
  in

  let (left, rest) = parse_atom tokens in
  parse_conj left rest

let parse_modal_string input =
  try
    let tokens = tokenize input in
    let (prop, remaining) = parse_modal tokens in
    match remaining with
    | [] -> prop
    | _ -> raise (ParseError "Unexpected tokens at end of input")
  with
  | ParseError msg -> raise (ParseError msg)
  | _ -> raise (ParseError "Unknown parsing error")

(** ========== Evaluation Interface ========== **)

(** Create valuation function from association list **)
let make_valuation_func valuations =
  fun prop ->
    try List.assoc prop valuations
    with Not_found -> false

(** Evaluate modal proposition (simplified version of extracted Coq code) **)
let rec eval_modal ctx = function
  | MProp s -> ctx.mc_valuation s
  | MBot -> false
  | MNeg p -> not (eval_modal ctx p)
  | MConj (p, q) -> (eval_modal ctx p) && (eval_modal ctx q)
  | MDisj (p, q) -> (eval_modal ctx p) || (eval_modal ctx q)
  | MImpl (p, q) -> (not (eval_modal ctx p)) || (eval_modal ctx q)
  | MBox p -> forall_accessible ctx p
  | MDia p -> exists_accessible ctx p

and forall_accessible ctx prop =
  List.for_all (fun world ->
    let new_ctx = { ctx with mc_world = world } in
    eval_modal new_ctx prop
  ) ctx.mc_accessible

and exists_accessible ctx prop =
  List.exists (fun world ->
    let new_ctx = { ctx with mc_world = world } in
    eval_modal new_ctx prop
  ) ctx.mc_accessible

(** Evaluate IEL operator **)
let rec eval_iel_operator ctx = function
  | IIdentity s -> ctx.mc_valuation s
  | IExperience s -> exists_accessible ctx (MProp s)
  | IUnification (op1, op2) ->
      (eval_iel_operator ctx op1) && (eval_iel_operator ctx op2)

(** Evaluate full IEL modal proposition **)
let rec eval_iel_modal ctx = function
  | IELBase mp -> eval_modal ctx mp
  | IELOp (op, mp) -> (eval_iel_operator ctx op) && (eval_iel_modal ctx mp)

(** ========== Runtime API ========== **)

(** High-level evaluation function for string input **)
let evaluate_modal_string world accessible_worlds valuations modal_string =
  try
    let prop = parse_modal_string modal_string in
    let ctx = {
      mc_world = world;
      mc_accessible = accessible_worlds;
      mc_valuation = make_valuation_func valuations;
    } in
    let result = eval_modal ctx prop in
    `Assoc [
      ("success", `Bool true);
      ("result", `Bool result);
      ("proposition", modal_prop_to_json prop);
      ("context", `Assoc [
        ("world", `String world);
        ("accessible", `List (List.map (fun w -> `String w) accessible_worlds));
        ("valuations", `Assoc (List.map (fun (k, v) -> (k, `Bool v)) valuations))
      ])
    ]
  with
  | ParseError msg ->
      `Assoc [
        ("success", `Bool false);
        ("error", `String ("Parse error: " ^ msg));
        ("input", `String modal_string)
      ]
  | e ->
      `Assoc [
        ("success", `Bool false);
        ("error", `String ("Evaluation error: " ^ Printexc.to_string e));
        ("input", `String modal_string)
      ]

(** Batch evaluation for multiple propositions **)
let evaluate_batch world accessible_worlds valuations propositions =
  let results = List.map (evaluate_modal_string world accessible_worlds valuations) propositions in
  `Assoc [
    ("batch_results", `List results);
    ("total_count", `Int (List.length propositions));
    ("context", `Assoc [
      ("world", `String world);
      ("accessible", `List (List.map (fun w -> `String w) accessible_worlds))
    ])
  ]

(** ========== Export for Python Interface ========== **)

(** Entry points for external calling (C-compatible) **)
let () =
  (* Register callbacks for Python interface *)
  Callback.register "eval_modal_string" evaluate_modal_string;
  Callback.register "eval_batch" evaluate_batch;
  Callback.register "parse_modal" parse_modal_string
