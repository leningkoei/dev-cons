select memory.id, memory.talk, battle.result from log
inner join memory on log.memory_id = memory.id
inner join battle on log.battle_id = battle.id
where log.created_at >= '2085-08-01' and log.created_at < '2087-10-20'
