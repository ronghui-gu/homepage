def addToList (result, name):
    result.append(name)

students = ["abcdef", "abc", "abcdefg"]

result = []
for i in range(len(students)):
    name = students[i]
    if len(name) > 5:
        addToList(result, name)
print(result)


def filterList (students):
    result = []
    for name in students:
        if len(name) > 5:
            addToList(result, name)
    return result

print(filterList(students))


import functools

def compose(*functions):
    def compose2(f, g):
        return lambda x: f(g(x))
    return functools.reduce(compose2, functions, lambda x: x)

compose(print, list, lambda l: filter(lambda name: len(name) > 5, l))
    (students)

def isNameLong (name):
    return len(name) > 5

print(
    list(
        filter(isNameLong, students)))


print(
    list(
        filter(lambda name: len(name) > 5,
                students)))

class Student:
  def __init__(self, name):
    self.name = name
    self.department = "CS"

students = [Student("abcdef"), Student("abc"), Student("abcdefg")]


def filterList (students):
    result = []
    for student in students:
        if student.name.__len__() > 5:
            result.append(student.name)
    return result

print(filterList(students))
