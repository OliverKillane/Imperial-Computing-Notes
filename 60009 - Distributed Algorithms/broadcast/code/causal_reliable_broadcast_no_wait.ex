defmodule Causal_Reliable_Broadcast_No_Wait do
  def start do
    receive do
      { :bind, client, urb } -> next(client, urb, [ ], MapSet.new)
    end
  end

  # past      -> messages that have been crb_broadcast or crb_delivered
  #              (the list of messages that are causally precede)
  # delivered -> messages that have been crb-delivered
  #
  # Message Formats:
  # { :crb_broadcast, msg }
  #
  # Note: m_past are the preceding messages
  # { :urb_deliver, from, { :crb_data, m_past, msg } }
  defp next(client, urb, past, delivered) do
    receive do
      { :crb_broadcast, msg } ->
        send urb, { :urb_broadcast, { :crb_data, past, msg} }

        # Add this message to the delivered messages
        new_past = past ++ [{ self(), msg }]

        next(client, urb, new_past, delivered)

      { :urb_deliver, from, { :crb_data, m_past, msg } } ->
        if msg in delivered do
          next(client, urb, past, delivered)
        else

          # specify all preceding messages as delivered (even if they have not yet been urb_delivered - message dropped)
          old_msgs =
            for { past_sender, past_msg } = past_data <- m_past,
                                                         past_msg not in delivered
              into: MapSet.new
            # syntax error here
            do send c, { :crb_deliver, past_sender, past_msg }
              past_data
          end

          # crb deliver this message
          send c, { :crb_deliver, from, msg }

          # old messages marked as delivered
          new_delivered = MapSet.put(MapSet.union(delivered, old_msgs), msg)
          new_past = past ++ old_msgs ++ [{from, msg}]

          next(client, urb, new_past, new_delivered)
        end
    end
  end
end
