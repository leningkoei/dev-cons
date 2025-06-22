select
Players.id,
sum(Items.damage * Inventories.count) as inventory_sum_damage
from Inventories
inner join Players on Inventories.user_id = Players.id
inner join Items on Inventories.item_id = Items.id
group by Players.id
