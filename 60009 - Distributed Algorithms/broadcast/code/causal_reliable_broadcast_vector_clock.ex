defmodule Causal_Reliable_Broadcast_Vector_Clock # waiting causal broadcast + vector clocks
  def start (pnum) do # we assume process id are numbers 1..N
    receive do
      { :bind, client, rb } -> next(client, rb, pnum, 0, Map.new, [ ])
    end
  end

  # vc   -> Vector Clock: a map (process -> No. messages crb delivered)
  # pnum -> This process's unique number
  #
  defp next(client, rb, pnum, rb_broadcasts, vc, pending) do
    receive do
      { :crb_broadcast, msg } ->
        # Create a new vector clock with this broadcast included
        vc2 = Map.put(vc, pnum, rb_broadcasts)

        # Broadcast (including updated vector clock)
        send rb, { :rb_broadcast, { :crb_data, vc2, msg }},

        next(client, rb, pnum, rb_broadcasts + 1, vc, pending)

      { :rb_deliver, sender, { :crb_data, s_vc, s_msg }} ->
        # deliver messages to client using pending messages and vector clock
        { new_vc, new_pending } = deliver(client, vc, pending ++ [{ sender, s_vc, s_msg }])

        next(client, rb, pnum, rb_broadcasts, new_vc, new_pending)
    end
  end

  # UNFINISHED
  defp deliver(client, vc, pending) do
    for pending_tuple <- pending, reduce: {vc, []} do
      {vc, still_pending} ->
        { sender, s_vc, s_msg } = pending_tuple
        if s_vc <= vc do # assume <= is true if s_vc[k] <= vc[k] for every entry k
          send c, { :crb_deliver, sender, s_msg }
          crb_deliveries = Map.get(vc, sender, 0) # 0 if empty
          vc = Map.put(vc, sender, crb_deliveries + 1)
          {vc, still_pending}
        else
          {vc, still_pending ++ [pending_tuple])
        end
    end
  end
end
