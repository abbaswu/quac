## Changelog
1. Change property-related code into non-property related code, e.g. a.property -> a.property()
2. Annotate classmethods
3. Annotate pendulum.__init__.py and pendulum._extension.helpers.py, since those are public functions accessed across the project recursively. The behaviour is dynamic and current inter-procedure mechanism is not fine-grained enough to handle such a dynamic behaviour. 
 