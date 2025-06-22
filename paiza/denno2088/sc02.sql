select memory.id, memory.talk from memory
-- inner join person on memory.person_id = person.id
inner join category on memory.category_id = category.id
where memory.importance >= 3
and category.name = "悲しみ"
