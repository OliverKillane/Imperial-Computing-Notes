defmodule FIFO_Reliable_Broadcast do # uses RB and sequence no's
  @initial_seq 0

  def start do
    receive do
      { :bind, client, rb } -> next(client, rb, @initial_seq, Map.new, [ ])
    end
  end

  # pseqno  -> for each process holds the seq_num of the next
  #            message to be frb-delivered from that process
  # pending –> messages that have been rb-delivered to this process and
  #            awaiting to be frb-delivered to the client
  #
  # Message formats:
  # { :frb_broadcast, msg }
  # { :rb_deliver, from, {:frb_data, {sender, msg, seq } } }
  defp next(client, rb, seq_num, pseqno, pending) do
    receive do
      { :frb_broadcast, msg } ->
        send rb, { :rb_broadcast, {:rb_data, {self(), msg, seq_num}}}
        next(client, rb, seq_num + 1, pseqno, pending)
      { :rb_deliver, _, {:frb_data, {sender, _, _} = frb_msg } } ->
        {new_pseqno, new_pending} = check_pending_and_deliver(client, sender, pseqno, pending ++ [frb_msg])
        next(client, rb, seq_num, new_pseqno, new_pending)
    end
  end

  defp check_pending_and_deliver(client, sender, pseqno, pending) do
    # returns the first frb message from sender where the process seq matches the message seq
    # If no sequence number exists in pseqno, we assume it is the first (0)
    case Enum.find(pending, fn {from, _, seq} -> from == sender and seq == Map.get(pseqno, from, @initial_seq ) end) do
      {_, msg, seq} = data ->
        send client, {:fdb_deliver, msg}
        new_pseqno = Map.put(pseqno, sender, seq + 1)
        new_pending = List.delete(pending, data)
        check_pending_and_deliver(client, sender, new_pseqno, new_pending)
      _ -> {pseqno, pending}
    end
  end
end
