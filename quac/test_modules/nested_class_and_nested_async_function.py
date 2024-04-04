import aiohttp
import asyncio
import re


class Outer:
    class Inner:
        @staticmethod
        def get_url():
            return "http://www.randomnumberapi.com/api/v1.0/random?min=100&max=200&count=5"


class OuterClass:
    outer_class_var = "I'm in the outer class"

    def __init__(self):
        self.outer_instance_var = "I'm in an instance of the outer class"

    @staticmethod
    def get_url():
        return "http://www.randomnumberapi.com/api/v1.0/random?min=100&max=200&count=5"
    
    def outer_method(self):
        def nested_function_1():
            print("Inside nested_function_1")

            def deeply_nested_function():
                print("Inside deeply_nested_function")

            deeply_nested_function()

        class NestedClass:
            nested_class_var = "I'm in the nested class"

            def __init__(self):
                self.nested_instance_var = "I'm in an instance of the nested class"

            def nested_method(self):
                print("Inside nested_method")

        nested_function_1()
        nested_instance = NestedClass()
        print(nested_instance.nested_class_var)
        print(nested_instance.nested_instance_var)
        nested_instance.nested_method()


async def fetch_and_process(url_fetcher):
    url = url_fetcher()
    try:
        async with aiohttp.ClientSession() as session:
            async with session.get(url) as resp:
                data = await resp.text()
                # Find all the numbers in the response
                numbers = [int(x) for x in re.findall(r'\d+', data)]
                # Calculate the average using a lambda function
                avg = (lambda nums: sum(nums) / len(nums))(numbers)
                return avg
    except Exception as e:
        print(f"An error occurred: {e}")

o = OuterClass()
