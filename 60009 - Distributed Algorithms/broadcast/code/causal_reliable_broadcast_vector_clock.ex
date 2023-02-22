defmodule Causal_Reliable_Broadcast_Vector_Clock do
  def start () do
    receive do
      { :bind, client, rb } -> next(client, rb, 0, Map.new, [ ])
    end
  end

  # client -> The client to deliver messages to
  # rb     -> Reliable broadcast (used by crb to broadcast)
  # vc     -> Vector Clock: a map (pid -> number of messages crb delivered)
  # pnum   -> This process's unique number
  defp next(client, rb, rb_broadcasts, vc, pending) do
    receive do
      { :crb_broadcast, msg } ->
        # Create a new vector clock with this broadcast included and send
        send_vc = Map.put(vc, self(), rb_broadcasts)
        send rb, { :rb_broadcast, { :crb_data, send_vc, msg }}

        # continue
        next(client, rb, rb_broadcasts + 1, vc, pending)

      { :rb_deliver, sender, { :crb_data, s_vc, s_msg }} ->
        # Add delivered messages to pending and determine which can now be delivered.
        { new_vc, new_pending } = deliver(client, vc, pending ++ [{ sender, s_vc, s_msg }])

        next(client, rb, rb_broadcasts, new_vc, new_pending)
    end
  end

  defp deliver(client, vc, pending) do
    for pending_tuple <- pending, reduce: {vc, []} do
      {vc, still_pending} ->
        { sender, s_vc, s_msg } = pending_tuple
        # <= is true if s_vc[p] <= vc[p] for every entry p
        if s_vc <= vc do
          # Deliver the message
          send c, { :crb_deliver, sender, s_msg }

          # Update the sender's entry in vector clock
          new_vc = Map.put(vc, sender, Map.get(vc, sender, 0) + 1)

          {new_vc, still_pending}
        else
          {vc, still_pending ++ [pending_tuple]}
        end
    end
  end
end
