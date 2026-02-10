module PickList = struct
  let reducer = Extracted.PickList.reducer

  let pick = Extracted.PickList.mk_do_pick
  let unpick = Extracted.PickList.mk_do_unpick

  let init default rest =
    Extracted.PickList.init_state default (Array.to_list rest)

  let picked s =
    Array.of_list (Extracted.PickList.picked s)

  let suggestions s =
    Array.of_list (Extracted.PickList.suggestions s)
end
