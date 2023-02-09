defmodule Perfect_Failure_Detector do
  def start do
    receive do
      { :bind, c, pl, processes, delay } ->
        # Send the first heartbeat request
        heartbeat_requests(delay)

        next(c, pl, processes, delay, processes, MapSet.new())
    end
  end

  defp next(c, pl, processes, delay, alive, crashed) do
    receive do
      # Send heartbeat requests over perfect link
      { :pl_deliver, from, :heartbeat_request } ->
        send pl, { :pl_send, from, :heartbeat_reply }
        next(c, pl, processes, delay, alive, crashed)

      # Receive heartbeat responses over perfect links
      { :pl_deliver, from, :heartbeat_reply } ->
        next(c, pl, processes, delay, MapSet.put(alive, from), crashed)

      # Timeout period expired
      # 1. Get all previously alive processes that did not respond (these have crashed)
      # 2. Send crashed to each
      :timeout ->
        newly_crashed =
          for p <- processes, p not in alive and p not in crashed, into: MapSet.new do p end

        # Inform process p of all newly crashed processes
        for p <- newly_crashed do send c, { :pfd_crash, p } end

        # Send new heartbeat requests over perfect links
        for p <- alive do send pl, { :pl_send, p, :heartbeat_request } end

        heartbeat_requests(delay)

        # Loop (empty set of alive, union set of old and newly crashed)
        next(c, pl, processes, delay, MapSet.new(), Mapset.union(crashed, newly_crashed))
    end
  end

  defp heartbeat_requests(delay) do
    # after delay milliseconds, timeout will be received by this process
    Process.send_after(self(), :timeout, delay)
  end
end
