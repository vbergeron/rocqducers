module PickList = struct
  let reduce = Extracted.PickList.reduce

  let pick = Extracted.PickList.do_pick
  let unpick = Extracted.PickList.do_unpick

  let init default rest =
    Extracted.PickList.init default (Array.to_list rest)

  let picked s =
    Array.of_list (Extracted.PickList.picked s)

  let suggestions s =
    Array.of_list (Extracted.PickList.suggestions s)
end

module Loader = struct
  let step = Extracted.Loader.step
  let init = Extracted.Loader.init_state

  let fetch = Extracted.Loader.mk_fetch
  let got_response = Extracted.Loader.mk_got_response
  let got_error = Extracted.Loader.mk_got_error
  let timed_out = Extracted.Loader.mk_timed_out
  let do_retry = Extracted.Loader.mk_do_retry

  let phase s = Extracted.Loader.phase s
  let cache s = Extracted.Loader.cache s
  let next_id s = Extracted.Loader.next_id s
  let retries s = Extracted.Loader.retries s

  let is_idle = Extracted.Loader.is_idle
  let is_loading = Extracted.Loader.is_loading
  let loading_rid = Extracted.Loader.loading_rid
  let is_loaded = Extracted.Loader.is_loaded
  let is_errored = Extracted.Loader.is_errored
end

module AsyncButton = struct

  let idle = Extracted.AsyncButton.Idle
  let loading = Extracted.AsyncButton.Loading

  let click = Extracted.AsyncButton.Click
  let success = Extracted.AsyncButton.Success
  let failure = Extracted.AsyncButton.Failure

  let reducer = Extracted.AsyncButton.reducer
end