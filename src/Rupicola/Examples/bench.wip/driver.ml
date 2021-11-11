let fnv1a (data: char list) =
  let p = 16777619L in
  let hash = 2166136261L in
  List.fold_left (fun (hash: int64) b -> Int64.mul (Int64.logxor hash (Int64.of_int (int_of_char b))) p) hash data

let () =
  let open Core in
  let open Core_bench in

  let bs = Bytes.of_string (In_channel.read_all "random.data") in
  let data = Bytes.to_list bs in

  Command.run (Bench.make_command [
    Bench.Test.create ~name:"id"
      (fun () -> ());
    Bench.Test.create ~name:"fnv1a"
      (fun () -> ignore (fnv1a data))
    ])
