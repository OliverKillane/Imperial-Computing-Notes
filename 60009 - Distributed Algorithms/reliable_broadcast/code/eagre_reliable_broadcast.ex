# Eagre reliable broadcast implemented using Best Effort Broadcast
# beb    <- the best effort broadcast process
# client <- the object broadcasting & being delivered
defmodule Eagre_Reliable_Broadcast do

  def start do
    receive do { :bind, client, beb } -> next(client, beb, MapSet.new) end
  end

  defp next(client, beb, delivered) do
    receive do
      { :rb_broadcast, msg } ->
        send beb, { :beb_broadcast, { :rb_data, our_id(), msg } }
        next(client, beb, delivered)
      { :beb_deliver, from, { :rb_data, sender, msg } = rb_m } ->
        if msg in delivered do
          # Message was already delivered, so can be ignored
          next(client, beb, delivered)
        else
          # Message is new, so add to delivered, deliver to c & rebroadcast
          send client, { :rb_deliver, sender, msg }
          send beb, { :beb_broadcast, rb_m }
          next(client, beb, MapSet.put(delivered, msg))
        end
    end
  end

end
