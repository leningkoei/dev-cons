-- select memory.id, memory.talk, person.name, battle.created_at from log
-- inner join battle on log.person_id = battle.person_id
-- inner join person on log.person_id = person.id
-- inner join memory on log.memory_id = memory.id
-- inner join category on memory.category_id = category.id
-- where person.importance = 5
-- and person.deleted_at = battle.created_at

-- Wrong Answer!!
-- select memory.id, memory.talk, person.name, battle.created_at from person
-- inner join battle on person.id = battle.person_id
-- inner join memory on person.id = memory.person_id
-- where person.importance = 5
-- and person.deleted_at = battle.created_at

select memory.id, memory.talk, person.name, battle.created_at from memory
inner join log on memory.id = log.memory_id
inner join battle on log.person_id = battle.person_id
inner join person on battle.person_id = person.id
where person.importance = 5
and person.deleted_at = battle.created_at
