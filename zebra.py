import copy
from abc import ABCMeta, abstractmethod

class Domain(object):
    def __init__(self, values):
        self.__values = values

    def __str__(self):
        return str(self.__values)

    def __len__(self):
        return len(self.__values)

    def __getitem__(self, item):
        return self.__values[item]

    def __eq__(self, other):
        return self.__values == other.__values

    def __ne__(self, other):
        return self.__values != other.__values

    @staticmethod
    def largest_domain(domains):
        return max(domains, key=len)

    def split_in_half(self):
        return Domain(self[:len(self) // 2]), Domain(self[len(self) // 2:])

    def is_empty(self):
        return len(self) == 0

    def is_reduced_to_only_one_value(self):
        return len(self) == 1


class Variable(object):
    def __init__(self, name, id, domain):
        self.name = name
        self.id = id
        self.domain = domain

    def set_domain(self, new_domain):
        self.domain = new_domain

    def get_domain(self):
        return self.domain

    def __str__(self):
        return str(self.id)


class Constraint(metaclass=ABCMeta): #define abstract class
    def __str__(self):
        return self.variables

    @abstractmethod
    def is_satisfied(self):
        pass

    @abstractmethod
    def reduction(self):
        pass


class Constraint_equality_var_var(Constraint):
    def __init__(self, variable_alpha, variable_beta):
        self.variable_alpha = variable_alpha
        self.variable_beta = variable_beta

    def __str__(self):
        return "The house for " + str(self.variable_alpha) + " needs to be the same as " + str(self.variable_beta)

    def is_satisfied(self):
        for elem1 in self.variable_alpha.get_domain():
            for elem2 in self.variable_beta.get_domain():
                if elem1 == elem2:
                    return True
        return False

    def reduction(self):
        new_domain = Domain(list(set(self.variable_alpha.domain).intersection(self.variable_beta.domain))) #using sets intersection operation
        self.variable_alpha.set_domain(new_domain)
        self.variable_beta.set_domain(new_domain)


class Constraint_equality_var_cons(Constraint):
    def __init__(self, variable_alpha, constant_c):
        self.variable_alpha = variable_alpha
        self.constant_c = constant_c

    def __str__(self):
        return "The house for " + str(self.variable_alpha) + " is: " + str(self.constant_c)

    def is_satisfied(self):
        if self.constant_c in self.variable_alpha.domain:
            return True
        return False

    def reduction(self):
        new_domain = Domain([self.constant_c])
        self.variable_alpha.set_domain(new_domain)


class Constraint_equality_var_plus_cons(Constraint):
    def __init__(self, variable_alpha, variable_beta, constant_c):
        self.variable_alpha = variable_alpha
        self.variable_beta = variable_beta
        self.constant_c = constant_c

    def __str__(self):
        return "The house for " + str(self.variable_alpha) + " is on the right of the house for " + str(
            self.variable_beta)

    def is_satisfied(self):
        for elem1 in self.variable_alpha.get_domain():
            for elem2 in self.variable_beta.get_domain():
                if elem1 == elem2 + self.constant_c:
                    return True
        return False

    def reduction(self):
        new_domain_alpha = []
        new_domain_beta = []
        for elem in self.variable_alpha.domain:
            for otherelem in self.variable_beta.domain:
                if elem == otherelem + self.constant_c:
                    new_domain_alpha.append(elem)
                    new_domain_beta.append(otherelem)
        new_domain_alpha = Domain(new_domain_alpha)
        new_domain_beta = Domain(new_domain_beta)
        self.variable_alpha.set_domain(new_domain_alpha)
        self.variable_beta.set_domain(new_domain_beta)


class Constraint_equality_plus_minus_cons(Constraint):
    def __init__(self, variable_alpha, variable_beta, constant_c):
        self.variable_alpha = variable_alpha
        self.variable_beta = variable_beta
        self.constant_c = constant_c

    def __str__(self):
        return "The house for " + str(self.variable_alpha) + " is next (right or left) to the house for " + str(
            self.variable_beta)

    def is_satisfied(self):
        for elem1 in self.variable_alpha.get_domain():
            for elem2 in self.variable_beta.get_domain():
                if abs(elem2 - elem1) == self.constant_c:
                    return True
        return False

    def reduction(self):
        new_domain_alpha = set([])
        new_domain_beta = set([])
        for elem in self.variable_alpha.domain:
            for otherelem in self.variable_beta.domain:
                if elem == otherelem + self.constant_c or otherelem == elem + self.constant_c:
                    new_domain_alpha.add(elem)
                    new_domain_beta.add(otherelem)
        new_domain_alpha = Domain(list(new_domain_alpha))
        new_domain_beta = Domain(list(new_domain_beta))
        self.variable_alpha.set_domain(new_domain_alpha)
        self.variable_beta.set_domain(new_domain_beta)


class Constraint_difference_var_var(Constraint):
    def __init__(self, variable_alpha, variable_beta):
        self.variable_alpha = variable_alpha
        self.variable_beta = variable_beta

    def __str__(self):
        return "The house for " + str(self.variable_alpha) + " needs to be different from " + str(self.variable_beta)

    def is_satisfied(self):
        if self.variable_alpha.domain.is_reduced_to_only_one_value() and self.variable_beta.domain.is_reduced_to_only_one_value():
            if self.variable_alpha.domain == self.variable_beta.domain:
                return False
        return True

    def reduction(self):

        if self.variable_alpha.get_domain().is_reduced_to_only_one_value():
            new_domain_beta = []
            for elem in self.variable_beta.domain:
                if elem not in self.variable_alpha.domain:
                    new_domain_beta.append(elem)
            new_domain_beta = Domain(new_domain_beta)
            self.variable_beta.set_domain(new_domain_beta)

        if self.variable_beta.get_domain().is_reduced_to_only_one_value():
            new_domain_alpha = []
            for elem in self.variable_alpha.domain:
                if elem not in self.variable_beta.domain:
                    new_domain_alpha.append(elem)
            new_domain_alpha = Domain(new_domain_alpha)
            self.variable_alpha.set_domain(new_domain_alpha)


class Problems(object):
    def __init__(self, variables, constraints):
        self.variables = variables
        self.constraints = constraints

    def __str__(self):
        print("Variables:")
        for elem in self.variables:
            print("Domain for", elem, "-", elem.get_domain())
        print("Constraints:")
        for elem in self.constraints:
            print(elem)
        return ""

    def domain_reduc(self):
        new_problem = copy.deepcopy(self) #deepcopy of current problem
        continue_loop = True
        while continue_loop:
            continue_loop = False
            domain_change_check = []
            for variable in new_problem.variables:
                domain_change_check += [variable.get_domain()] #will be used to check if there was a domain change after applying domain reduction
            for constraint in new_problem.constraints:
                constraint.reduction() #applies domain reduction to all variables as per the constraints
            for i in range(len(domain_change_check)):
                if domain_change_check[i] != new_problem.variables[i].get_domain(): #check for a domain change
                    continue_loop = True
            for variable in new_problem.variables:
                if variable.get_domain().is_empty(): #check for an empty domain
                    continue_loop = False
        return new_problem

    def domain_splitting(self):
        reduced_problem = self.domain_reduc()

        if any(variable.get_domain().is_empty() for variable in reduced_problem.variables): #base case 1
            return None  # Impossible to find a solution
        if all(variable.get_domain().is_reduced_to_only_one_value() for variable in reduced_problem.variables): #base case 2
            return reduced_problem.variables #solution found!
        else:
            for variable in reduced_problem.variables:
                if len(variable.get_domain()) > 1: #search for a domain to split
                    for domain in variable.get_domain().split_in_half():
                        variable.set_domain(domain)
                        solution = reduced_problem.domain_splitting() #recursive call
                        if solution: #if the solution is None (cf base case 1), this is False
                            return solution


def create_variable(name, id):
    return Variable(name, id, Domain([1, 2, 3, 4, 5]))

#create variables
country1 = "Spain"
country2 = "Ukraine"
country3 = "Japan"
country4 = "Norway"
country5 = "England"

norvegian = create_variable("Norvegian", country4)
spaniard = create_variable("Spain", country1)
englishdude = create_variable("England", country5)
ukrainian = create_variable("Ukraine", country2)
japanese = create_variable("Japan", country3)

country_list = [norvegian, spaniard, englishdude, ukrainian, japanese]

color1 = "blue"
color2 = "green"
color3 = "ivory"
color4 = "red"
color5 = "yellow"

blue = create_variable("blue", color1)
green = create_variable("green", color2)
ivory = create_variable("ivory", color3)
red = create_variable("red", color4)
yellow = create_variable("yellow", color5)

color_list = [blue, green, ivory, red, yellow]

pet1 = "dog"
pet2 = "snails"
pet3 = "fox"
pet4 = "horse"
pet5 = "zebra"

dog = create_variable("dog", pet1)
snail = create_variable("snails", pet2)
fox = create_variable("fox", pet3)
horse = create_variable("horse", pet4)
zebra = create_variable("zebra", pet5)

pet_list = [dog, snail, fox, horse, zebra]

bev1 = "coffee"
bev2 = "milk"
bev3 = "tea"
bev4 = "orange"
bev5 = "water"

coffee = create_variable("coffee", bev1)
milk = create_variable("milk", bev2)
tea = create_variable("tea", bev3)
orange = create_variable("orange", bev4)
water = create_variable("water", bev5)

bev_list = [coffee, milk, tea, orange, water]

game1 = 'Snakes and Ladders'
game2 = 'Cluedo'
game3 = 'Pictionary'
game4 = 'Travel the World'
game5 = 'Backgammon'

snakes_and_ladders = create_variable("Snakes and Ladders", game1)
cluedo = create_variable("Cluedo", game2)
pictionary = create_variable("Pictionary", game3)
travel_the_world = create_variable("Travel the World", game4)
backgammon = create_variable("Backgammon", game5)

game_list = [snakes_and_ladders, cluedo, pictionary, travel_the_world, backgammon]

#create constraints
constraint_list = [Constraint_equality_var_var(englishdude, red),
                   Constraint_equality_var_var(spaniard, dog),
                   Constraint_equality_var_var(coffee, green),
                   Constraint_equality_var_var(ukrainian, tea),
                   Constraint_equality_var_plus_cons(green, ivory, 1),
                   Constraint_equality_var_var(snakes_and_ladders, snail),
                   Constraint_equality_var_var(cluedo, yellow),
                   Constraint_equality_var_cons(milk, 3),
                   Constraint_equality_var_cons(norvegian, 1),
                   Constraint_equality_plus_minus_cons(pictionary, fox, 1),
                   Constraint_equality_plus_minus_cons(cluedo, horse, 1),
                   Constraint_equality_var_var(travel_the_world, orange),
                   Constraint_equality_var_var(japanese, backgammon),
                   Constraint_equality_plus_minus_cons(norvegian, blue, 1)]


def constraint_generator(list_of_var):
    constraints = []
    for i in range(len(list_of_var)):
        for j in range(i + 1, len(list_of_var)):
            constraints.append(Constraint_difference_var_var(list_of_var[i], list_of_var[j]))
    return constraints


variables_list = []

#put them in a list
for elem in (bev_list, pet_list, color_list, game_list, country_list):
    constraint_list.extend(constraint_generator(elem))
    variables_list.extend(elem)

#create the problem
my_problem = Problems(variables_list, constraint_list)

#solve the problem
my_solution = my_problem.domain_splitting()

solution_to_display = [[], [], [], [], []] #This is only used for the purpose of displaying the solution in a neat way

#display solution
print("The solution is:")
for elem in my_solution:
    for i in range(5):
        if elem.get_domain() == Domain([i + 1]):
            solution_to_display[i].append(elem)

for i, house in enumerate(solution_to_display):
    print("House #" + str(i + 1))
    for variable in house:
        print(variable, "\t\t", end="")
    print()
    print()
