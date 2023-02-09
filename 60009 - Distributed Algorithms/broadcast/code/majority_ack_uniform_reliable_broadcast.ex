defmodule Majority_Ack_Uniform_Reliable_Broadcast do
  def start do
    receive do
      { :bind, client, beb, n_processes } ->
      next(client, beb, n_processes, MapSet.new, MapSet.new, Map.new)
    end
  end

  # client      -> the client using uniform reliable broadcast
  # beb         -> the best effort broadcast module used
  # n_processes -> Need to know the number of processes to determine if more than half have delivered
  # delivered   -> messages that been urb_delivered
  # pending     -> messages that have been beb_broadcast but need to be urb-delivered
  # bebd        -> foreach message, the set of processes that have beb-delivered (seen) it
  defp next(client, beb, n_processes, delivered, pending, bebd) do
    receive do

      # Broadcast a message to all
      { :urb_broadcast, msg } ->
        # Use best effort broadcast to send message
        send beb, { :beb_broadcast, { :urb_data, our_id(), msg } }

        # Asynchronously check if the message can be delivered
        send self(), :can_deliver

        # Mark message as pending
        new_pending = MapSet.put(pending, { our_id(), msg })

        next(client, beb, n_processes, delivered, new_pending, bebd)

      # Receive via best effort broadcast
      { :beb_deliver, from, { :urb_data, sender, msg } = urb_m } ->
        # Get the processes that have seen this message, and add from to that set
        msg_pset = Map.get(bebd, msg, MapSet.new)
        next_bebd = Map.put(bebd, msg, MapSet.put(msg_pset, from))

        # Asynchronously check if the message can be delivered
        send self(), :can_deliver

        # If the message has previously been recieved & placed in pending (do
        # nothing), else we must add it to pending.
        if { sender, msg } in pending do
          next (client, beb, n_processes, delivered, pending, next_bebd)
        else
          send beb, { :beb_broadcast, urb_m }
          new_pending = MapSet.put(pending, { sender, msg })
          next(client, beb, n_processes, delivered, new_pending, next_bebd)
        end

      # Determine if a best effort broadcast delivery can be uniform reliably delivered
      :can_deliver ->
        # Can only deliver if
        # - Message not already delivered
        # - Message has been delivered by a majority of other processes
        new_delivered_msgs =
          for { sender, msg } <- pending,
                                 msg not in delivered and
                                 MapSet.size(bebd[msg]) > n_processes/2
            into: MapSet.new
          do send client, { :urb_deliver, sender, msg }
            msg
        end
        new_delivered = MapSet.union(delivered, new_delivered_msgs)
        next(client, beb, n_processes, new_delivered, pending, bebd)
    end
  end
end
